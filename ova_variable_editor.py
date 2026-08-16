#!/usr/bin/env python3
"""Jade OVA/OFC binary variable viewer/editor.

The Jade source in ``Libraries/AIinterp/Sources/AIload.c`` defines the OVA
variable-description stream.  It is *not* an ASCII ``ova`` marker followed by
variable names.  The stream starts with a byte count for ``AI_tdst_VarInfo``
records (12 bytes each), followed by a byte count and fixed 30-byte
``AI_tdst_EditorVarInfo`` names.  Some extracted Universe BINs are truncated
inside that fixed-size name table, so this parser deliberately accepts a
structurally valid prefix and reports the truncation instead of falling back to
unrelated ASCII strings such as ``gao``/``RLI``.
"""

from __future__ import annotations

import hashlib
import ctypes
import os
import re
import shutil
import struct
import tkinter as tk
from dataclasses import dataclass
from pathlib import Path
from tkinter import filedialog, messagebox, ttk


MARKER = b"ova"
CONTEXT = 48
AI_MAX_LEN_VAR = 30
OVA_INFO_SIZE = 12
LEGACY_BF_HEADER_SIZE = 68
LEGACY_BF_FILE_ENTRY_SIZE = 84
LEGACY_BF_FILE_TABLE_ENTRY_SIZE = 8
LZO_BLOCK_SIZE = 131072
OFC_EXT = b".ofc"
OVA_EXT = b".ova"

# Verified against the two supplied Xbox SOT demo Big Files.  This is not a
# guessed byte patch: the retail "cheats on" file changes four linked entries,
# so copying only the Universe byte would be an incomplete game patch.
SOT_DEMO_OFF_SHA256 = "490d4a764ae90d1e74ff6f2c877540f6fa474a506863c1dba029aa6aec79dca7"
SOT_DEMO_ON_SHA256 = "0964b31d5400359de5116b4abb1541cac5f08fcdcc7d3570eb6ecd1189aa9e46"
SOT_DEMO_CHEAT_VALUE_OFFSET = 0x580

# IDs from Jade's Libraries/AIinterp/Sources/Types/AIdeftyp.h.
AI_TYPE_IDS = {32, 33, 34, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51}
AI_CATEG_NAMES = {
    0: "CATEG_TYPE",
    1: "CATEG_TYPE",
    2: "CATEG_KEYWORD",
    3: "CATEG_FUNCTION",
    4: "CATEG_FIELD",
    5: "CATEG_LOCALVAR",
    6: "CATEG_LOCALVARARRAY",
    7: "CATEG_LOCALVARARRAY2",
    8: "CATEG_LOCALVARARRAY3",
    10: "CATEG_LOCALVARARRAYREF",
    11: "CATEG_LOCALVARARRAY2REF",
    12: "CATEG_LOCALVARARRAY3REF",
    20: "CATEG_GLOBALVAR",
    21: "CATEG_GLOBALVARARRAY",
    22: "CATEG_GLOBALVARARRAY2",
    23: "CATEG_GLOBALVARARRAY3",
    25: "CATEG_INITLOCALVARARRAY",
    26: "CATEG_EVENTPARAM",
    27: "CATEG_POPPROC",
    28: "CATEG_LOCALVARREF",
    29: "CATEG_POPPROCREF",
    31: "CATEG_ENDTREE",
}


@dataclass
class OvaHit:
    offset: int
    before: bytes
    after: bytes


@dataclass
class OvaVariable:
    name: str
    offset: int
    source: str
    var_offset: int | None = None
    var_type: int | None = None
    flags: int | None = None
    structure_base: int | None = None
    value_absolute: int | None = None


@dataclass
class AiArtifact:
    extension: str
    offset: int
    key: int | None
    source: str


@dataclass
class ResourceRef:
    kind: str
    name: str
    offset: int
    key: int | None = None
    source: str = "GAO resource browser"


@dataclass
class AiNode:
    offset: int
    l_param: int
    w_param: int
    flags: int
    c_type: int
    description: str


@dataclass
class OvaStructure:
    base: int
    count: int
    names_base: int
    names_size: int
    complete_names: int
    truncated: bool
    init_base: int | None = None
    init_size: int | None = None
    source_format: str = "Jade"
    records_base: int | None = None
    names_available: bool = True
    names_encrypted: bool = False
    container_end: int | None = None
    name_slots: int | None = None


@dataclass
class BinaryDiff:
    offset: int
    before: int
    after: int


@dataclass
class BigFileEntry:
    index: int
    position: int
    key: int
    size: int
    name: str
    parent: int
    fat_index: int
    first_index: int
    compressed: bool = False
    data_header_size: int = 0
    compression: str = "none"


@dataclass
class BigFileInfo:
    path: Path
    version: int
    max_file: int
    max_dir: int
    size_fat: int
    num_fat: int
    universe_key: int
    encrypted_fat: bool
    entries: list[BigFileEntry]


def _read_big_header(stream) -> BigFileInfo:
    header = stream.read(44)
    if len(header) != 44:
        raise ValueError("File .bf troppo corto per contenere l'header Jade.")
    magic, version, max_file, max_dir, _max_key, _root, _free_file, _free_dir, size_fat, num_fat, universe_key = struct.unpack("<4s10I", header)
    encrypted = magic == b"BUG\0"
    if magic not in (b"BIG\0", b"BUG\0"):
        raise ValueError(f"Header BIG non riconosciuto: {magic!r}")
    if not 1 <= num_fat <= 64 or size_fat <= 0:
        raise ValueError("Header .bf non plausibile (size FAT / numero FAT).")

    entries: list[BigFileEntry] = []
    descriptor_pos = 44
    for fat_index in range(num_fat):
        stream.seek(descriptor_pos)
        raw = stream.read(24)
        if len(raw) != 24:
            raise ValueError(f"Descriptor FAT #{fat_index} troncato.")
        fat_max_file, _fat_max_dir, pos_fat, next_pos_fat, first_index, _last_index = struct.unpack("<6I", raw)
        if fat_max_file > size_fat:
            raise ValueError(f"FAT #{fat_index} non plausibile.")

        stream.seek(pos_fat)
        file_table = stream.read(fat_max_file * 8)
        if len(file_table) != fat_max_file * 8:
            raise ValueError(f"Tabella file FAT #{fat_index} troncata.")

        # BIG_tdst_FileExt::st_ToSave is 88 bytes in the supplied Jade source:
        # 4 length + 3*4 links + 4-byte L_time_t + 64-byte name + 4 P4 revision.
        # The extended table is indexed by the *global* file index, so the
        # table starts after max-file slots, not after fat_max_file slots.
        ext_base = pos_fat + size_fat * 8
        stream.seek(ext_base)
        ext_table = stream.read(fat_max_file * 88)
        if len(ext_table) != fat_max_file * 88:
            raise ValueError(f"Tabella nomi FAT #{fat_index} troncata.")

        for i in range(fat_max_file):
            position, key = struct.unpack_from("<2I", file_table, i * 8)
            if key == 0xFFFFFFFF:
                continue
            ext = ext_table[i * 88 : (i + 1) * 88]
            size_on_disk = struct.unpack_from("<I", ext, 0)[0]
            # The first 20 bytes are the serialized links/time. The 64-byte
            # name begins at offset 20, matching BIG_tdst_FileExt in Jade.
            parent = struct.unpack_from("<I", ext, 12)[0]
            raw_name = ext[20:84].split(b"\0", 1)[0]
            name = raw_name.decode("ascii", errors="replace").strip()
            if not name:
                name = f"<file_{first_index + i:06d}>"
            entries.append(
                BigFileEntry(
                    index=first_index + i,
                    position=position,
                    key=key,
                    size=size_on_disk,
                    name=name,
                    parent=parent,
                    fat_index=fat_index,
                    first_index=first_index,
                    compressed=bool(size_on_disk & 0x80000000),
                )
            )

        if next_pos_fat != 0xFFFFFFFF:
            descriptor_pos = next_pos_fat - 24
        else:
            descriptor_pos += 24

    entries.sort(key=lambda e: (e.fat_index, e.index))
    return BigFileInfo(stream.name if hasattr(stream, "name") else Path(""), version, max_file, max_dir, size_fat, num_fat, universe_key, encrypted, entries)


def _looks_like_pop_lzo(data: bytes) -> bool:
    """Detect the POP v37/v38 block-LZO wrapper used by the supplied tools."""
    if len(data) < 18:
        return False
    dec_size, enc_size = struct.unpack_from("<2I", data, 0)
    if dec_size <= enc_size or enc_size <= 0:
        return False
    if dec_size > 16 * 1024 * 1024:
        return False
    # This mirrors PopTools' DecompressFile() test: the first LZO block has
    # the 0x99C0FFEE marker at byte 13 or 14 of the entry payload.
    magic = b"\x99\xC0\xFF\xEE"
    return data[13:17] == magic or data[14:18] == magic


def _load_lzo_bridge() -> ctypes.CDLL:
    """Load the local x64 minilzo bridge built from Jade's supplied source."""
    candidates = [
        Path(__file__).with_name("lzo_compat.dll"),
        Path(__file__).with_name("lzo.dll"),
        Path(r"C:\Users\Admin\Desktop\Giochi\PopTools\bf_repacker_2018_05_23_1419\lzo.dll"),
    ]
    errors = []
    for candidate in candidates:
        if not candidate.exists():
            continue
        try:
            lib = ctypes.CDLL(str(candidate))
            fn = lib.lzo_bridge_decompress
            fn.argtypes = [
                ctypes.POINTER(ctypes.c_ubyte),
                ctypes.c_uint,
                ctypes.POINTER(ctypes.c_ubyte),
                ctypes.POINTER(ctypes.c_uint),
            ]
            fn.restype = ctypes.c_int
            return lib
        except (OSError, AttributeError) as exc:
            errors.append(f"{candidate}: {exc}")
    raise RuntimeError(
        "Supporto LZO POP non disponibile. Manca lzo_compat.dll accanto a ova_variable_editor.py."
    )


_LZO_BRIDGE: ctypes.CDLL | None = None


def decompress_pop_lzo(data: bytes) -> bytes:
    """Decompress POP's sequence of little-endian LZO blocks."""
    global _LZO_BRIDGE
    if _LZO_BRIDGE is None:
        _LZO_BRIDGE = _load_lzo_bridge()
    pos = 0
    output = bytearray()
    while pos + 8 <= len(data):
        dec_size, enc_size = struct.unpack_from("<2I", data, pos)
        pos += 8
        if dec_size == 0 and enc_size == 0:
            break
        if enc_size > len(data) - pos:
            raise ValueError("Blocco LZO POP troncato.")
        block = data[pos:pos + enc_size]
        pos += enc_size
        if dec_size == enc_size:
            output.extend(block)
        else:
            src = (ctypes.c_ubyte * len(block)).from_buffer_copy(block)
            dst = (ctypes.c_ubyte * dec_size)()
            out_size = ctypes.c_uint(dec_size)
            rc = _LZO_BRIDGE.lzo_bridge_decompress(src, enc_size, dst, ctypes.byref(out_size))
            if rc != 0 or out_size.value != dec_size:
                raise ValueError(f"Decompressione LZO POP fallita (rc={rc}, output={out_size.value}, atteso={dec_size}).")
            output.extend(bytes(dst[:out_size.value]))
        if dec_size < LZO_BLOCK_SIZE:
            break
    return bytes(output)


def _read_legacy_bigfile(path: Path) -> BigFileInfo:
    """Read the v37/v38 BIG layout used by the supplied Prince of Persia tools."""
    with path.open("rb") as stream:
        header = stream.read(LEGACY_BF_HEADER_SIZE)
        if len(header) != LEGACY_BF_HEADER_SIZE:
            raise ValueError("File .bf troppo corto per l'header POP/Jade legacy.")
        magic, version, fcount, dcount, _unk2, _unk3, capacity, _unk4, universe_key, fcount2, dcount2, file_id_offset, _unk5, _unk6, _last = struct.unpack("<4sIIIQQIIIIIIiII", header)
        if magic != b"BIG\0":
            raise ValueError(f"Header BIG legacy non riconosciuto: {magic!r}")
        if version not in (37, 38):
            raise ValueError(f"Layout legacy richiesto per v37/v38, trovato v{version}.")
        if not (1 <= fcount <= capacity <= 2_000_000):
            raise ValueError("Header .bf legacy non plausibile (fcount/capacity).")

        file_id_base = LEGACY_BF_HEADER_SIZE
        file_entry_base = file_id_base + capacity * LEGACY_BF_FILE_TABLE_ENTRY_SIZE
        file_table_end = file_id_base + fcount * LEGACY_BF_FILE_TABLE_ENTRY_SIZE
        file_entry_end = file_entry_base + fcount * LEGACY_BF_FILE_ENTRY_SIZE
        file_size = path.stat().st_size
        if file_entry_end > file_size:
            raise ValueError("Tabella FileEntry legacy troncata.")

        entries: list[BigFileEntry] = []
        for i in range(fcount):
            stream.seek(file_id_base + i * 8)
            position, key = struct.unpack("<2I", stream.read(8))
            stream.seek(file_entry_base + i * LEGACY_BF_FILE_ENTRY_SIZE)
            ext = stream.read(LEGACY_BF_FILE_ENTRY_SIZE)
            size_on_disk, _next, _prev, parent, _timestamp = struct.unpack_from("<5I", ext, 0)
            raw_name = ext[20:84].split(b"\0", 1)[0]
            name = raw_name.decode("ascii", errors="replace").strip()
            if not name:
                name = f"<file_{i:06d}>"
            if position + 4 > file_size:
                raise ValueError(f"Entry legacy #{i} punta oltre il file.")
            available = min(size_on_disk, file_size - (position + 4))
            stream.seek(position + 4)
            prefix = stream.read(min(32, available))
            compressed = _looks_like_pop_lzo(prefix)
            entries.append(
                BigFileEntry(
                    index=i,
                    position=position,
                    key=key,
                    size=size_on_disk,
                    name=name,
                    parent=parent,
                    fat_index=0,
                    first_index=0,
                    compressed=compressed,
                    data_header_size=4,
                    compression="POP-LZO" if compressed else "none",
                )
            )
        entries.sort(key=lambda e: e.index)
        return BigFileInfo(path, version, capacity, dcount, capacity, 1, universe_key, False, entries)


def read_bigfile(path: Path) -> BigFileInfo:
    with path.open("rb") as stream:
        raw_header = stream.read(8)
    if len(raw_header) >= 8 and raw_header[:4] == b"BIG\0":
        version = struct.unpack_from("<I", raw_header, 4)[0]
        if version in (37, 38):
            return _read_legacy_bigfile(path)
    with path.open("rb") as stream:
        info = _read_big_header(stream)
    info.path = path
    return info


def read_bigfile_entry(path: Path, entry: BigFileEntry) -> bytes:
    with path.open("rb") as stream:
        stream.seek(entry.position + entry.data_header_size)
        length = entry.size & 0x7FFFFFFF
        data = stream.read(length)
        if len(data) != length:
            raise ValueError(f"Entry {entry.name} troncata nel .bf.")
    if entry.compressed and entry.compression == "POP-LZO":
        return decompress_pop_lzo(data)
    return data


def find_bigfile_ova_entries(info: BigFileInfo) -> list[BigFileEntry]:
    """Return entries that are likely OVA/Universe payloads without reading the whole BF."""
    result = []
    for entry in info.entries:
        lower = entry.name.lower()
        # In complete game Big Files the same OVA variable-description block
        # is embedded in GAO entries as well. Demo dumps often expose it as
        # Univers_oin_*.bin, which is why the older filter appeared to work.
        # Keep GAOs in the selectable set, but inspect only one entry at a
        # time so the UI does not duplicate the same variables once per GAO.
        if lower.endswith((".ova", ".bin", ".gao", ".wow")):
            result.append(entry)
    return result


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def find_ova(data: bytes) -> list[OvaHit]:
    hits: list[OvaHit] = []
    start = 0
    while True:
        pos = data.find(MARKER, start)
        if pos < 0:
            break
        lo = max(0, pos - CONTEXT)
        hi = min(len(data), pos + len(MARKER) + CONTEXT)
        hits.append(OvaHit(pos, data[lo:pos], data[pos + 3 : hi]))
        start = pos + 1
    return hits


def find_variables(data: bytes) -> list[OvaVariable]:
    """Decode Jade ``AI_tdst_VarInfo`` + fixed 30-byte editor names.

    The important detail for Universe BIN extraction is that the enclosing
    file can end before the advertised name table does.  We therefore accept a
    candidate when its header, all 12-byte records and name-table size are
    coherent and at least two complete names are available.  A truncated tail
    is reported in the source text rather than producing false ASCII hits.
    A general ASCII scan is deliberately not returned as variables: GAO/BIN
    payloads contain many unrelated labels and accepting them made the BF
    auto-selector claim an OVA decode where none had occurred.
    """
    structures = find_ova_structures(data)
    if not structures:
        return []

    # POP v37/v38 is the format used by the PoP Trilogy Big Files. Prefer it
    # over the later generic Jade scan: a random 32-bit value in a large GAO
    # can otherwise look like a valid ``size_r``/30-byte-name stream.
    pop_structures = [s for s in structures if s.source_format == "POP37/38"]
    if pop_structures:
        structure = max(pop_structures, key=lambda s: (s.complete_names, s.name_slots or 0, -s.base))
    else:
        # Prefer the candidate with the most complete names. The exact size/count/
        # 30-byte name-table relationship is the primary structural discriminator;
        # type IDs are retained as metadata rather than used as a hard filter.
        structure = max(structures, key=lambda s: (s.complete_names, -s.base))
    result: list[OvaVariable] = []
    for i in range(structure.count):
        if structure.source_format == "POP37/38":
            info = (structure.records_base or 0) + i * OVA_INFO_SIZE
            _num_elem, packed_type_flags, var_offset = struct.unpack_from("<III", data, info)
            var_type = packed_type_flags & 0xFFFF
            flags = (packed_type_flags >> 16) & 0xFFFF
            if structure.names_available:
                slot = structure.names_base + i * AI_MAX_LEN_VAR
                raw = data[slot:min(slot + AI_MAX_LEN_VAR, len(data))]
            else:
                slot = info
                raw = b""
        else:
            slot = structure.names_base + i * AI_MAX_LEN_VAR
            raw = data[slot:min(slot + AI_MAX_LEN_VAR, len(data))]
            info = structure.base + 4 + i * OVA_INFO_SIZE
            var_offset, _num_elem, var_type, flags = struct.unpack_from("<iihh", data, info)
        if slot >= len(data):
            break
        if structure.names_available:
            name = raw.split(b"\0", 1)[0].decode("ascii", errors="ignore")
            if not name or not _valid_identifier(name):
                continue
        else:
            # Retail PoP37/38 Big Files can contain the engine var records but
            # omit the editor-name array entirely. The records are still real
            # OVA variables; using an explicit synthetic label is preferable
            # to turning unrelated GAO/texture ASCII into fake variable names.
            name = f"OVA_{i + 1:03d}"
        value_absolute = None
        if structure.init_base is not None and structure.init_size is not None:
            if 0 <= var_offset < structure.init_size:
                value_absolute = structure.init_base + var_offset
        suffix = ""
        if not structure.names_available:
            if structure.names_encrypted:
                suffix = f" (editor names encrypted/unavailable: {structure.count} records)"
            else:
                suffix = f" (editor names unavailable: {structure.count} records)"
        elif structure.truncated:
            suffix = f" (truncated: {structure.complete_names}/{structure.count} names)"
        result.append(
            OvaVariable(
                name=name,
                offset=slot,
                source=f"{structure.source_format} OVA @ 0x{structure.base:08X}{suffix}",
                var_offset=var_offset,
                var_type=var_type,
                flags=flags,
                structure_base=structure.base,
                value_absolute=value_absolute,
            )
        )
    return result


def find_ova_structures(data: bytes) -> list[OvaStructure]:
    """Locate structurally valid Jade OVA descriptor streams."""
    candidates: list[OvaStructure] = _find_pop_ova_structures(data)
    for base in range(0, max(0, len(data) - 8)):
        if base + 8 > len(data):
            break
        size_r = struct.unpack_from("<I", data, base)[0]
        if not size_r or size_r % OVA_INFO_SIZE:
            continue
        count = size_r // OVA_INFO_SIZE
        if count < 1 or count > 4096 or base + 4 + size_r + 4 > len(data):
            continue
        names_size = struct.unpack_from("<I", data, base + 4 + size_r)[0]
        if names_size != count * AI_MAX_LEN_VAR:
            continue
        names_base = base + 8 + size_r
        available = max(0, len(data) - names_base)
        available_slots = min(count, (available + AI_MAX_LEN_VAR - 1) // AI_MAX_LEN_VAR)
        if available_slots < 1:
            continue

        valid_names = 0
        for i in range(count):
            info = base + 4 + i * OVA_INFO_SIZE
            if i < available_slots:
                raw = data[names_base + i * AI_MAX_LEN_VAR:min(names_base + (i + 1) * AI_MAX_LEN_VAR, len(data))]
                name = raw.split(b"\0", 1)[0].decode("ascii", errors="ignore")
                if name and _valid_identifier(name):
                    valid_names += 1
        if valid_names < max(1, min(count, 2)):
            continue

        # The rest of the OVA stream is: var2-size, var2 records/strings,
        # init-buffer size, init bytes, then initial function keys.  We can
        # resolve the init-buffer absolute address only when the whole prefix
        # is present.  For the truncated Universe extraction this remains None.
        init_base, init_size = _find_init_buffer_after_names(data, names_base + names_size)
        candidates.append(
            OvaStructure(
                base=base,
                count=count,
                names_base=names_base,
                names_size=names_size,
                complete_names=valid_names,
                truncated=(available < names_size),
                init_base=init_base,
                init_size=init_size,
            )
        )
    return candidates


def ova_diagnostic_report(data: bytes, label: str = "buffer") -> list[str]:
    """Return a compact, reproducible explanation of the OVA parse result.

    This deliberately reports the descriptor even when its editor-name table
    is unavailable.  That distinction is essential for retail PoP BIGs: the
    OVA records can be valid while the names are encrypted, so an ASCII scan
    would be a misleading diagnostic.
    """
    structures = find_ova_structures(data)
    markers = find_ova(data)
    lines = [
        f"[ANALISI] {label}: {len(data):,} B | marker ASCII 'ova': {len(markers)} | descrittori OVA: {len(structures)}"
    ]
    if markers:
        offsets = ", ".join(f"0x{hit.offset:08X}" for hit in markers[:8])
        suffix = " …" if len(markers) > 8 else ""
        lines.append(f"  marker 'ova' a {offsets}{suffix}")
    if not structures:
        fallback = find_ascii_fallback(data)
        lines.append(
            f"  NESSUN descrittore strutturale: fallback ASCII produrrebbe {len(fallback)} stringhe (non OVA affidabili)."
        )
        return lines
    for structure in sorted(structures, key=lambda s: (s.base, s.source_format)):
        state = "nomi in chiaro" if structure.names_available else (
            "nomi cifrati/trasformati" if structure.names_encrypted else "tabella nomi non inclusa nell'entry"
        )
        records = f" records @ 0x{structure.records_base:08X}" if structure.records_base is not None else ""
        boundary = f" | fine entry interna 0x{structure.container_end:08X}" if structure.container_end is not None else ""
        lines.append(
            f"  OK {structure.source_format} @ 0x{structure.base:08X}:{records} "
            f"{structure.count} record da {OVA_INFO_SIZE} B | nomi @ 0x{structure.names_base:08X} "
            f"({structure.names_size} B; {state}; validi {structure.complete_names}/{structure.count}){boundary}"
        )
    variables = find_variables(data)
    synthetic = sum(variable.name.startswith("OVA_") for variable in variables)
    lines.append(f"  RISULTATO: {len(variables)} variabili mostrate ({synthetic} con nome sintetico).")
    return lines


def _find_pop_ova_structures(data: bytes) -> list[OvaStructure]:
    """Locate the older OVA descriptor embedded in PoP v37/v38 binarized data."""
    candidates: list[OvaStructure] = []
    marker = b"\x99\xC0\xFF\xEE"
    start = 0
    while True:
        base = data.find(marker, start)
        if base < 0:
            break
        start = base + 4
        if base + 20 > len(data):
            continue
        kind, _unused, var_bytes = struct.unpack_from("<3I", data, base + 4)
        if kind != 0x0A000109 or not var_bytes or var_bytes % OVA_INFO_SIZE:
            continue
        count = var_bytes // OVA_INFO_SIZE
        if count > 4096:
            continue
        records_base = base + 20
        names_base = records_base + var_bytes
        names_span = count * AI_MAX_LEN_VAR
        # A POP ``Univers_oin`` BIN is itself a stream of inner Jade entries:
        # [size][0x99C0FFEE][file id][payload].  The OVA marker is the inner
        # entry magic, therefore base-4 is its size and base-8 its header.
        # Never read a purported name table past this boundary: retail builds
        # often omit editor names, and the following entry looks like random
        # data if it is incorrectly treated as 30-byte names.
        container_end = len(data)
        if base >= 4:
            entry_size = struct.unpack_from("<I", data, base - 4)[0]
            candidate_end = base + 8 + entry_size
            if candidate_end <= len(data):
                container_end = candidate_end
        # Retail/Prototype POP builds are not always editor dumps.  In
        # particular SOT_PROTO_ps2 stores only a short encrypted editor-name
        # area, followed immediately by the VarInfo2 section.  Assuming
        # count*30 here makes the parser consume VarInfo2/init data as if it
        # were names, which is exactly why the old parser reported nonsense.
        # Detect the shorter name area from the serialization boundary:
        # [name bytes][VarInfo2 byte-size, multiple of 20][VarInfo2...].
        detected_name_span = _detect_pop_name_span(
            data, names_base, count, container_end, names_span
        )
        name_slots = (detected_name_span + AI_MAX_LEN_VAR - 1) // AI_MAX_LEN_VAR
        names_available = False
        valid = 0
        if detected_name_span == names_span:
            names_available = True
            for i in range(count):
                p = names_base + i * AI_MAX_LEN_VAR
                raw = data[p:p + AI_MAX_LEN_VAR]
                name = raw.split(b"\0", 1)[0].decode("ascii", errors="ignore")
                if name and _valid_identifier(name):
                    valid += 1
            if valid < count:
                names_available = False
        elif detected_name_span:
            # A short table is still meaningful metadata. It can contain
            # encrypted/obfuscated editor names; the following bytes are not
            # names and must never be shown through the ASCII fallback.
            for i in range(name_slots):
                p = names_base + i * AI_MAX_LEN_VAR
                raw = data[p:p + AI_MAX_LEN_VAR]
                name = raw.split(b"\0", 1)[0].decode("ascii", errors="ignore")
                if name and _valid_identifier(name):
                    valid += 1
        # Retail PoP37/38 builds can keep the complete 30-byte editor-name
        # region but replace its plaintext with high-entropy/encrypted bytes.
        # It is still a real OVA descriptor: the engine records immediately
        # before this region are authoritative.  Never send such a descriptor
        # to the ASCII fallback, because that produces unrelated GAO/text
        # strings and was the source of the misleading "ASCII" result.
        names_encrypted = bool(
            detected_name_span
            and not names_available
            and valid == 0
            and detected_name_span <= names_span
        )
        # POP37/38 stores the initial-value buffer directly after the fixed
        # 30-byte name table.  Unlike the later Jade stream there is no
        # VarInfo2/string-size prefix here.  Offsets in the VarInfo records
        # are relative to the *size field* (not its following payload), hence
        # a variable at offset 4 is the first byte of initial values.
        init_base = init_size = None
        names_end = names_base + detected_name_span
        if names_available and names_end + 4 <= container_end:
            possible_size = struct.unpack_from("<I", data, names_end)[0]
            if possible_size and possible_size <= container_end - names_end:
                init_base, init_size = names_end, possible_size
        candidates.append(
            OvaStructure(
                base=base,
                count=count,
                names_base=names_base,
                names_size=detected_name_span,
                complete_names=valid,
                truncated=not names_available,
                source_format="POP37/38",
                records_base=records_base,
                names_available=names_available,
                names_encrypted=names_encrypted,
                container_end=container_end,
                name_slots=name_slots,
                init_base=init_base,
                init_size=init_size,
            )
        )
    return candidates


def _detect_pop_name_span(
    data: bytes,
    names_base: int,
    count: int,
    container_end: int,
    full_span: int,
) -> int:
    """Find the actual POP editor-name area without consuming later sections.

    Normal retail Universe entries have ``count * 30`` bytes of plaintext
    names followed by the initial-value size.  Some prototype builds instead
    contain a shorter encrypted name area followed by ``VarInfo2``.  The Jade
    source defines ``AI_tdst_EditorVarInfo2`` as 20 bytes on the 32-bit target,
    so a plausible multiple-of-20 size immediately after a 30-byte boundary
    is a strong format boundary.
    """
    if names_base >= container_end:
        return 0
    full_end = names_base + full_span
    if full_end <= container_end:
        # A complete plaintext table wins immediately. Do not reinterpret a
        # valid name table just because a later 20-byte-aligned value happens
        # to occur inside it.
        valid = 0
        for i in range(count):
            p = names_base + i * AI_MAX_LEN_VAR
            raw = data[p:p + AI_MAX_LEN_VAR]
            name = raw.split(b"\0", 1)[0].decode("ascii", errors="ignore")
            if name and _valid_identifier(name):
                valid += 1
        if valid >= max(2, min(count, 8)):
            return full_span

    # Search the shorter editor-name payload.  The prototype does not pad this
    # encrypted area to 30-byte boundaries: its boundary is at 0x3B8 (208
    # bytes) followed by a 500-byte VarInfo2 section.  Scan byte boundaries so
    # we can recognize that real serialization instead of guessing a 30-byte
    # slot count.
    search_end = min(full_end, container_end)
    for end in range(names_base + 32, search_end + 1):
        if end + 4 > container_end:
            break
        var2_size = struct.unpack_from("<I", data, end)[0]
        if not var2_size or var2_size > 1024 * 1024 or var2_size % 20:
            continue
        if end + 4 + var2_size > container_end:
            continue
        # If another 32-bit field follows VarInfo2, accept either a known BIG
        # key or a zero/size-like field. This avoids stopping inside ciphertext
        # merely because four random bytes happen to be divisible by 20.
        after = end + 4 + var2_size
        if after + 4 <= container_end:
            next_value = struct.unpack_from("<I", data, after)[0]
            if next_value not in (0, 0xFFFFFFFF) and (next_value & 0xFF000000) not in (0xCC000000, 0xFF000000):
                continue
        return end - names_base
    # No editor-name section was serialized in this entry. The remaining
    # bytes belong to engine/init data and must not be relabeled as names.
    return 0


def _find_init_buffer_after_names(data: bytes, pos: int) -> tuple[int | None, int | None]:
    """Best-effort decode of the post-name OVA editor/initial-value prefix."""
    if pos + 8 > len(data):
        return None, None
    var2_size = struct.unpack_from("<I", data, pos)[0]
    if var2_size > 1024 * 1024 or var2_size % 20:
        return None, None
    strings_size = struct.unpack_from("<I", data, pos + 4)[0]
    p = pos + 8
    if var2_size > len(data) - p:
        return None, None
    p += var2_size
    if strings_size > len(data) - p:
        return None, None
    p += strings_size
    if p + 4 > len(data):
        return None, None
    init_size = struct.unpack_from("<I", data, p)[0]
    init_base = p + 4
    if init_size > len(data) - init_base:
        return None, None
    return init_base, init_size


def find_ascii_fallback(data: bytes) -> list[OvaVariable]:
    """Fallback for files that contain no recognizable Jade OVA descriptor."""
    found: dict[tuple[int, str], OvaVariable] = {}
    for i in range(len(data)):
        if 32 <= data[i] < 127 and (i == 0 or not (32 <= data[i - 1] < 127)):
            j = i
            while j < len(data) and 32 <= data[j] < 127:
                j += 1
            text = data[i:j].decode("ascii", errors="ignore")
            for match in re.finditer(r"[A-Za-z_][A-Za-z0-9_]{2,}", text):
                name = match.group()
                if _valid_identifier(name) and name.lower() not in {"ova", "ofc"}:
                    found.setdefault((i + match.start(), name), OvaVariable(name, i + match.start(), "ASCII fallback"))
    return sorted(found.values(), key=lambda v: v.offset)


def _valid_identifier(name: str) -> bool:
    return (
        3 <= len(name) < AI_MAX_LEN_VAR
        and any(c.isalpha() or c == "_" for c in name)
        and all(c.isalnum() or c in "_()" for c in name)
    )


def find_ai_artifacts(data: bytes) -> list[AiArtifact]:
    """Find every explicit .ova/.ofc reference and record its preceding key."""
    artifacts: list[AiArtifact] = []
    for ext in (OVA_EXT, OFC_EXT):
        start = 0
        while True:
            pos = data.find(ext, start)
            if pos < 0:
                break
            key = struct.unpack_from("<I", data, pos - 4)[0] if pos >= 4 else None
            artifacts.append(AiArtifact(ext.decode("ascii"), pos, key, "extension reference"))
            start = pos + 1
    return sorted(artifacts, key=lambda a: a.offset)


def find_ai_nodes(data: bytes) -> list[AiNode]:
    """Decode the 8-byte ``AI_tdst_Node`` records used by Jade AI trees.

    The source defines the record as LONG + short + char + char.  A GAO can
    contain several unrelated byte streams, so only the longest coherent run
    ending in CATEG_ENDTREE is accepted.  These records are shown as TTT in
    the resource browser to match the terminology used by the reference tool.
    """
    best: list[AiNode] = []
    # Look for END TREE first. This avoids re-scanning the same long prefix at
    # every possible start offset in large .wow files.
    for end in range(3, len(data), 4):
        if data[end] != 31:
            continue
        start = end - 7
        while start >= 0 and end - start < 4096 * 8:
            if data[start + 7] > 63:
                start += 8
                break
            start -= 8
        start = max(0, start)
        nodes: list[AiNode] = []
        pos = start
        while pos <= end - 7 and len(nodes) < 4096:
            l_param, w_param, flags, c_type = struct.unpack_from("<ihBB", data, pos)
            if c_type > 63:
                nodes = []
                break
            nodes.append(AiNode(pos, l_param, w_param, flags, c_type, AI_CATEG_NAMES.get(c_type, f"CATEG_{c_type}")))
            pos += 8
        if nodes and nodes[-1].c_type == 31 and len(nodes) >= 2 and len(nodes) > len(best):
            best = nodes
    return best


def find_resource_refs(data: bytes, key_map: dict[int, BigFileEntry] | None = None) -> list[ResourceRef]:
    """Build the Resource Browser view for a GAO/BIN payload.

    OVA/OFC are resolved from BIG keys when the containing BF is available.
    TTT represents the serialized Jade AI node/tree records (the orange items
    visible in the reference application), so standalone BIN/GAO files still
    get a useful tree even without a BF key table.
    """
    refs: list[ResourceRef] = []
    seen: set[tuple[str, int, int | None]] = set()
    if key_map:
        for pos in range(0, max(0, len(data) - 3), 4):
            key = struct.unpack_from("<I", data, pos)[0]
            entry = key_map.get(key)
            if entry is None:
                continue
            ext = Path(entry.name).suffix.lower()
            if ext not in {".ova", ".ofc"}:
                continue
            kind = "OVA" if ext == ".ova" else "OFC"
            sig = (kind, pos, key)
            if sig not in seen:
                refs.append(ResourceRef(kind, entry.name, pos, key))
                seen.add(sig)

    for node in find_ai_nodes(data):
        refs.append(ResourceRef("TTT", node.description, node.offset, None, "Jade AI node"))
    return refs


def diff_bytes(before: bytes, after: bytes) -> list[BinaryDiff]:
    limit = min(len(before), len(after))
    result = [BinaryDiff(i, before[i], after[i]) for i in range(limit) if before[i] != after[i]]
    if len(before) != len(after):
        longer = after if len(after) > len(before) else before
        for i in range(limit, len(longer)):
            result.append(BinaryDiff(i, before[i] if i < len(before) else -1, after[i] if i < len(after) else -1))
    return result


def hex_line(data: bytes, base: int) -> str:
    return f"0x{base:08X}: " + " ".join(f"{b:02X}" for b in data)


class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("OVA Variable Editor")
        self.geometry("1120x820")
        self.minsize(900, 680)
        self.dark_mode = False
        self.style = ttk.Style(self)
        self._setup_theme()
        self.path: Path | None = None
        self.original = b""
        self.working = b""
        self.hits: list[OvaHit] = []
        self.variables: list[OvaVariable] = []
        self.jade_variables: list[OvaVariable] = []
        self.ascii_variables: list[OvaVariable] = []
        self.variable_mode = "jade"
        self.artifacts: list[AiArtifact] = []
        self.resource_refs: list[ResourceRef] = []
        self.ai_nodes: list[AiNode] = []
        self.big_info: BigFileInfo | None = None
        self.big_entries: list[BigFileEntry] = []
        self.big_entry: BigFileEntry | None = None
        self.direct_compressed = False
        self.comparison_path: Path | None = None
        self.comparison_data = b""
        self.dirty = False
        self._build()

    def _setup_theme(self) -> None:
        """Configure the complete light/dark palette used by the editor."""
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass
        self._apply_theme()

    def _apply_theme(self) -> None:
        if self.dark_mode:
            bg, surface, field = "#1e1f22", "#2b2d31", "#17181a"
            fg, muted, select = "#f2f3f5", "#b5bac1", "#4752c4"
            border = "#3f4147"
        else:
            bg, surface, field = "#f2f2f2", "#ffffff", "#ffffff"
            fg, muted, select = "#202124", "#5f6368", "#cfe2ff"
            border = "#c7c7c7"

        self.configure(bg=bg)
        self.style.configure("TFrame", background=bg)
        self.style.configure("TLabel", background=bg, foreground=fg)
        self.style.configure("TLabelframe", background=bg, foreground=fg)
        self.style.configure("TLabelframe.Label", background=bg, foreground=fg)
        self.style.configure("TButton", background=surface, foreground=fg, bordercolor=border, padding=(8, 5))
        self.style.map("TButton", background=[("active", select), ("disabled", field)], foreground=[("disabled", muted)])
        self.style.configure("TEntry", fieldbackground=field, foreground=fg, insertcolor=fg, bordercolor=border)
        self.style.configure("TCombobox", fieldbackground=field, background=surface, foreground=fg, arrowcolor=fg, bordercolor=border)
        self.style.map("TCombobox", fieldbackground=[("readonly", field)], foreground=[("readonly", fg)])
        self.style.configure("TNotebook", background=bg, bordercolor=border)
        self.style.configure("TNotebook.Tab", background=surface, foreground=fg, padding=(10, 5))
        self.style.map("TNotebook.Tab", background=[("selected", select)], foreground=[("selected", fg)])
        self.style.configure("TPanedwindow", background=bg)
        self.style.configure("Treeview", background=field, fieldbackground=field, foreground=fg, bordercolor=border, rowheight=25)
        self.style.configure("Treeview.Heading", background=surface, foreground=fg, bordercolor=border, padding=5)
        self.style.map("Treeview", background=[("selected", select)], foreground=[("selected", fg)])
        self.style.configure("Vertical.TScrollbar", background=surface, troughcolor=bg, bordercolor=border, arrowcolor=fg)
        self.style.configure("Horizontal.TScrollbar", background=surface, troughcolor=bg, bordercolor=border, arrowcolor=fg)
        self.style.configure("TCheckbutton", background=bg, foreground=fg)
        self.style.map("TCheckbutton", foreground=[("disabled", muted)])
        self.style.configure("TSeparator", background=border)
        if hasattr(self, "hex_text"):
            self.hex_text.configure(bg=field, fg=fg, insertbackground=fg, selectbackground=select, selectforeground=fg)
        if hasattr(self, "log_text"):
            self.log_text.configure(bg=field, fg=fg, insertbackground=fg, selectbackground=select, selectforeground=fg)
        if hasattr(self, "status"):
            self.status.configure(background=surface, foreground=fg)

    def _build(self) -> None:
        root = ttk.Frame(self, padding=10)
        root.pack(fill="both", expand=True)

        top = ttk.Frame(root)
        top.pack(fill="x", pady=(0, 8))
        ttk.Button(top, text="Importa .BF / .BIN", command=self.open_file).pack(side="left")
        ttk.Button(top, text="Confronta con BIN…", command=self.compare_file).pack(side="left", padx=6)
        ttk.Button(top, text="Salva con nome…", command=self.save_as).pack(side="left", padx=6)
        ttk.Button(top, text="Ripristina", command=self.reset).pack(side="left")
        self.variable_mode_btn = ttk.Button(top, text="OVA: Jade reale", command=self.toggle_variable_mode)
        self.variable_mode_btn.pack(side="left", padx=6)
        self.theme_btn = ttk.Button(top, text="🌙 Modalità scura", command=self.toggle_theme)
        self.theme_btn.pack(side="right")
        self.file_label = ttk.Label(top, text="Nessun file caricato")
        self.file_label.pack(side="left", padx=12)

        info = ttk.LabelFrame(root, text="File")
        info.pack(fill="x", pady=(0, 8))
        self.info_label = ttk.Label(info, text="Importa un file BIN per iniziare.")
        self.info_label.pack(anchor="w", padx=8, pady=6)

        bf_select = ttk.Frame(info)
        bf_select.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Label(bf_select, text="Entry OVA/BIN/GAO/WOW nel .BF:").pack(side="left")
        self.big_entry_combo = ttk.Combobox(bf_select, state="disabled", width=90)
        self.big_entry_combo.pack(side="left", fill="x", expand=True, padx=8)
        self.big_entry_combo.bind("<<ComboboxSelected>>", self.on_big_entry_selected)

        body = ttk.Panedwindow(root, orient="horizontal")
        body.pack(fill="both", expand=True)
        left = ttk.Frame(body, padding=(0, 0, 8, 0))
        right = ttk.Frame(body, padding=(8, 0, 0, 0))
        body.add(left, weight=1)
        body.add(right, weight=2)

        self.left_tabs = ttk.Notebook(left)
        self.left_tabs.pack(fill="both", expand=True)

        vars_tab = ttk.Frame(self.left_tabs, padding=(0, 5, 5, 0))
        refs_tab = ttk.Frame(self.left_tabs, padding=(0, 5, 5, 0))
        big_tab = ttk.Frame(self.left_tabs, padding=(0, 5, 5, 0))
        self.left_tabs.add(vars_tab, text="Variabili OVA")
        self.left_tabs.add(refs_tab, text="Resource Browser")
        self.left_tabs.add(big_tab, text="Entry nel .BF")

        ttk.Label(vars_tab, text="Variabili OVA rilevate").pack(anchor="w")
        ttk.Label(vars_tab, text="Jade OVA = decodifica strutturale; ASCII = fallback esplorativo").pack(anchor="w")
        cols = ("index", "name", "offset", "type", "source")
        tree_frame = ttk.Frame(vars_tab)
        tree_frame.pack(fill="both", expand=True, pady=(5, 0))
        self.tree = ttk.Treeview(tree_frame, columns=cols, show="headings", selectmode="browse")
        self.tree.heading("index", text="#")
        self.tree.heading("name", text="Variabile")
        self.tree.heading("offset", text="Offset")
        self.tree.heading("type", text="Tipo")
        self.tree.heading("source", text="Origine")
        self.tree.column("index", width=45, anchor="center")
        self.tree.column("name", width=190, anchor="w")
        self.tree.column("offset", width=100, anchor="center")
        self.tree.column("type", width=65, anchor="center")
        self.tree.column("source", width=140, anchor="w")
        self.tree.pack(in_=tree_frame, side="left", fill="both", expand=True)
        tree_scroll = ttk.Scrollbar(tree_frame, orient="vertical", command=self.tree.yview)
        tree_scroll.pack(side="right", fill="y")
        self.tree.configure(yscrollcommand=tree_scroll.set)
        self.tree.bind("<<TreeviewSelect>>", self.on_select)

        ref_cols = ("index", "extension", "name", "offset", "key", "source")
        ttk.Label(refs_tab, text="Legenda: OVA grigio  •  OFC azzurro  •  TTT arancione").pack(anchor="w")
        ref_frame = ttk.Frame(refs_tab)
        ref_frame.pack(fill="both", expand=True)
        self.artifact_tree = ttk.Treeview(ref_frame, columns=ref_cols, show="headings", selectmode="browse")
        for col, title in (("index", "#"), ("extension", "Tipo"), ("name", "Risorsa / nodo"), ("offset", "Offset"), ("key", "BIG_KEY"), ("source", "Origine")):
            self.artifact_tree.heading(col, text=title)
        self.artifact_tree.column("index", width=40, anchor="center")
        self.artifact_tree.column("extension", width=70, anchor="center")
        self.artifact_tree.column("name", width=220, anchor="w")
        self.artifact_tree.column("offset", width=90, anchor="center")
        self.artifact_tree.column("key", width=110, anchor="center")
        self.artifact_tree.column("source", width=110, anchor="w")
        self.artifact_tree.pack(side="left", fill="both", expand=True)
        ref_scroll = ttk.Scrollbar(ref_frame, orient="vertical", command=self.artifact_tree.yview)
        ref_scroll.pack(side="right", fill="y")
        self.artifact_tree.configure(yscrollcommand=ref_scroll.set)
        self.artifact_tree.bind("<Double-1>", self.on_resource_double_click)
        self.artifact_tree.tag_configure("OVA", foreground="#8a8a8a")
        self.artifact_tree.tag_configure("OFC", foreground="#38a9e8")
        self.artifact_tree.tag_configure("TTT", foreground="#f39c12")

        ttk.Label(big_tab, text="File .ova / .bin / .gao indicizzati nel Big File").pack(anchor="w")
        big_search = ttk.Frame(big_tab)
        big_search.pack(fill="x", pady=(5, 5))
        ttk.Label(big_search, text="Filtro:").pack(side="left")
        self.big_filter_var = tk.StringVar()
        ttk.Entry(big_search, textvariable=self.big_filter_var).pack(side="left", fill="x", expand=True, padx=6)
        self.big_filter_var.trace_add("write", lambda *_: self.refresh_big_tree())
        big_cols = ("index", "name", "size", "position", "key", "fat")
        big_tree_frame = ttk.Frame(big_tab)
        big_tree_frame.pack(fill="both", expand=True)
        self.big_tree = ttk.Treeview(big_tree_frame, columns=big_cols, show="headings", selectmode="browse")
        for col, title in (("index", "#"), ("name", "Entry"), ("size", "Bytes"), ("position", "Posizione"), ("key", "BIG_KEY"), ("fat", "FAT")):
            self.big_tree.heading(col, text=title)
        self.big_tree.column("index", width=70, anchor="center")
        self.big_tree.column("name", width=300, anchor="w")
        self.big_tree.column("size", width=90, anchor="e")
        self.big_tree.column("position", width=110, anchor="center")
        self.big_tree.column("key", width=110, anchor="center")
        self.big_tree.column("fat", width=50, anchor="center")
        self.big_tree.pack(side="left", fill="both", expand=True)
        big_scroll = ttk.Scrollbar(big_tree_frame, orient="vertical", command=self.big_tree.yview)
        big_scroll.pack(side="right", fill="y")
        self.big_tree.configure(yscrollcommand=big_scroll.set)
        self.big_tree.bind("<<TreeviewSelect>>", self.on_big_tree_selected)

        ttk.Label(right, text="Dettaglio e modifica").pack(anchor="w")
        detail = ttk.Frame(right)
        detail.pack(fill="x", pady=6)
        self.hit_label = ttk.Label(detail, text="Seleziona un marker.")
        self.hit_label.grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 8))

        ttk.Label(detail, text="Offset booleano relativo al valore OVA:").grid(row=1, column=0, sticky="w")
        self.offset_var = tk.StringVar(value="")
        ttk.Entry(detail, textvariable=self.offset_var, width=10).grid(row=1, column=1, sticky="w", padx=6)
        ttk.Label(detail, text="(es. -1, +4, +16)").grid(row=1, column=2, sticky="w")
        ttk.Button(detail, text="Cerca candidati 00/01", command=self.find_candidates).grid(row=1, column=3, padx=8)

        self.candidates = ttk.Combobox(detail, state="readonly", width=46)
        self.candidates.grid(row=2, column=0, columnspan=4, sticky="we", pady=6)
        self.candidates.bind("<<ComboboxSelected>>", self.use_candidate)

        actions = ttk.Frame(right)
        actions.pack(fill="x", pady=5)
        self.true_btn = ttk.Button(actions, text="Imposta TRUE (01)", command=lambda: self.set_bool(1))
        self.false_btn = ttk.Button(actions, text="Imposta FALSE (00)", command=lambda: self.set_bool(0))
        self.true_btn.pack(side="left")
        self.false_btn.pack(side="left", padx=6)

        ttk.Label(right, text="Anteprima bytes (hex)").pack(anchor="w", pady=(12, 3))
        self.hex_text = tk.Text(right, height=8, wrap="none", font=("TkFixedFont", 10))
        self.hex_text.pack(fill="both", expand=True)
        self.hex_text.configure(state="disabled")

        log_bar = ttk.Frame(right)
        log_bar.pack(fill="x", pady=(10, 3))
        ttk.Label(log_bar, text="Console diagnostica BF / OVA").pack(side="left")
        ttk.Button(log_bar, text="Pulisci log", command=self.clear_log).pack(side="right")
        self.log_text = tk.Text(right, height=10, wrap="word", font=("TkFixedFont", 9))
        self.log_text.pack(fill="both", expand=True)
        self.log_text.configure(state="disabled")

        self.status = ttk.Label(root, text="Pronto", relief="sunken", anchor="w")
        self.status.pack(fill="x", pady=(8, 0))

        self._apply_theme()

    def clear_log(self) -> None:
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")

    def on_resource_double_click(self, _event=None) -> None:
        """Open an OVA/OFC resource when its BIG key is known."""
        selection = self.artifact_tree.selection()
        if not selection or self.big_info is None:
            return
        item = self.artifact_tree.item(selection[0])
        values = item.get("values", ())
        if len(values) < 5 or not str(values[4]).startswith("0x"):
            return
        try:
            key = int(str(values[4]), 16)
        except ValueError:
            return
        for i, entry in enumerate(self.big_entries):
            if entry.key == key:
                self.big_entry_combo.current(i)
                self.load_big_entry(entry)
                return

    def log(self, message: str) -> None:
        """Append an event to the visible diagnostic terminal and stdout."""
        self.log_text.configure(state="normal")
        self.log_text.insert("end", message.rstrip() + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")
        print(message, flush=True)

    def log_ova_analysis(self, data: bytes, label: str) -> None:
        for line in ova_diagnostic_report(data, label):
            self.log(line)

    def toggle_theme(self) -> None:
        self.dark_mode = not self.dark_mode
        self.theme_btn.configure(text="☀ Modalità chiara" if self.dark_mode else "🌙 Modalità scura")
        self._apply_theme()

    def open_file(self) -> None:
        name = filedialog.askopenfilename(
            title="Importa BIN o Big File Jade",
            filetypes=[("Jade / POP resources", "*.bf *.bin *.ova *.ofc *.gao *.wow"), ("Jade Big Files", "*.bf"), ("BIN files", "*.bin"), ("OVA/OFC/GAO/WOW", "*.ova *.ofc *.gao *.wow"), ("Tutti i file", "*.*")],
        )
        if not name:
            return
        path = Path(name)
        if path.suffix.lower() == ".bf":
            self.open_bigfile(path)
            return
        self.clear_log()
        self.log(f"[FILE] Apertura diretta: {path} ({path.stat().st_size:,} B)")
        try:
            data = path.read_bytes()
        except OSError as exc:
            messagebox.showerror("Errore", f"Impossibile leggere il file:\n{exc}")
            return
        # A standalone Univers_oin_*.bin from PoP37/38 uses the same block-LZO
        # wrapper as a .BF entry.  The decompressed stream starts with the
        # 0x99C0FFEE descriptor and is the stream AI_ul_CallbackLoadVars reads.
        # Without this step the parser sees the compression header and can
        # incorrectly fall through to unrelated ASCII strings.
        self.direct_compressed = _looks_like_pop_lzo(data)
        if self.direct_compressed:
            compressed_size = len(data)
            try:
                data = decompress_pop_lzo(data)
            except (RuntimeError, ValueError) as exc:
                self.log(f"[ERRORE] Decompressione POP-LZO fallita: {exc}")
                messagebox.showerror("Errore LZO", f"Impossibile decomprimere il BIN POP:\n{exc}")
                return
            self.log(f"[LZO] Wrapper POP rilevato: {compressed_size:,} B -> {len(data):,} B decompressi")
        else:
            self.log("[LZO] Nessun wrapper POP-LZO rilevato.")
        self.path = path
        self.original = data
        self.working = bytearray(data)
        self.big_info = None
        self.big_entries = []
        self.big_entry = None
        self.big_entry_combo["values"] = ()
        self.big_entry_combo.set("")
        self.big_entry_combo.state(["disabled"])
        self.hits = find_ova(data)
        self.dirty = False
        self.file_label.config(text=self.path.name)
        self.jade_variables = find_variables(data)
        self.ascii_variables = find_ascii_fallback(data)
        self.variables = self.jade_variables if self.variable_mode == "jade" else self.ascii_variables
        self.log_ova_analysis(data, path.name)
        compression_text = " • POP-LZO decompresso per l'analisi" if self.direct_compressed else ""
        self.info_label.config(text=f"{len(data):,} bytes • SHA-256 {sha256(data)[:16]}… • {len(self.variables)} variabili • {len(self.hits)} marker 'ova'{compression_text}")
        self.artifacts = find_ai_artifacts(data)
        self.ai_nodes = find_ai_nodes(data)
        self.resource_refs = find_resource_refs(data)
        self.refresh_tree()
        self.status.config(text=f"Caricato: {len(self.jade_variables)} OVA Jade • {len(self.ai_nodes)} TTT • {len(self.artifacts) + len(self.resource_refs)} riferimenti")

    def open_bigfile(self, path: Path) -> None:
        self.clear_log()
        self.log(f"[BF] Apertura: {path}")
        try:
            info = read_bigfile(path)
        except (OSError, ValueError, MemoryError) as exc:
            self.log(f"[ERRORE] Header/indice BIG non leggibile: {exc}")
            messagebox.showerror("Errore Big File", f"Impossibile leggere il .bf:\n{exc}")
            return

        self.log(
            f"[BF] Header OK: BIG v{info.version}; FAT={info.num_fat}; file={len(info.entries):,}; "
            f"universe key=0x{info.universe_key:08X}; FAT {'cifrata' if info.encrypted_fat else 'non cifrata'}"
        )

        self.path = path
        self.big_info = info
        self.big_entries = find_bigfile_ova_entries(info)
        self.big_entry = None
        self.original = b""
        self.working = bytearray()
        self.dirty = False
        self.file_label.config(text=f"{path.name}  [BIG v{info.version}]")
        encrypted_text = "FAT cifrata" if info.encrypted_fat else "FAT non cifrata"
        self.info_label.config(
            text=(
                f"{path.stat().st_size:,} bytes • BIG v{info.version} • {info.num_fat} FAT • "
                f"{len(info.entries):,} file indicizzati • {len(self.big_entries)} entry candidate • {encrypted_text}"
            )
        )
        values = [self._big_entry_label(entry) for entry in self.big_entries]
        self.big_entry_combo["values"] = values
        self.big_entry_combo.state(["!disabled"] if values else ["disabled"])
        if values:
            # Prefer the Universe variable entry. In PoP v37/v38 it is a late
            # entry (hundreds/thousands of files into the FAT), so a bounded
            # scan from index 0 would never find it reliably.
            preferred = sorted(
                enumerate(self.big_entries),
                key=lambda pair: (
                    0 if pair[1].name.lower().startswith("univers_oin_") else
                    1 if pair[1].name.lower() == "univers.ova" else
                    2 if pair[1].name.lower().endswith(".ova") else
                    3 if pair[1].name.lower().endswith(".gao") else 4,
                    pair[0],
                ),
            )
            default_index = None
            fallback_index = None
            for i, entry in preferred:
                try:
                    data = read_bigfile_entry(path, entry)
                except (OSError, ValueError) as exc:
                    self.log(f"[SKIP] #{entry.index} {entry.name}: lettura/decompressione fallita: {exc}")
                    continue
                self.log(
                    f"[PROVA] #{entry.index} {entry.name}: {entry.size & 0x7FFFFFFF:,} B su disco -> "
                    f"{len(data):,} B {'(POP-LZO)' if entry.compressed else '(non compressa)'}"
                )
                if fallback_index is None:
                    fallback_index = i
                # A tiny placeholder .bin is technically readable but does
                # not give the variable list the user expects. Complete game
                # BFs commonly store the OVA description in GAOs, so accept a
                # structurally decoded GAO as soon as one is found. We still
                # keep the old bounded fallback for unrelated .bin entries.
                variables = find_variables(data)
                if (
                    variables
                    and (
                        entry.name.lower().startswith("univers_oin_")
                        or entry.name.lower().endswith((".ova", ".gao", ".wow"))
                    )
                    or (i < 128 and (variables or find_ova(data) or find_ai_artifacts(data)))
                ):
                    self.log(f"[SELEZIONE] #{entry.index} scelta automaticamente: {len(variables)} variabili decodificate.")
                    default_index = i
                    break
                if i >= 128 and info.version not in (37, 38):
                    break
            if default_index is None:
                default_index = fallback_index
            if default_index is not None:
                self.big_entry_combo.current(default_index)
                self.load_big_entry(self.big_entries[default_index])
                self.status.config(text=f"Big File aperto: {len(values)} entry OVA/BIN/GAO indicizzate")
            else:
                self.log("[AVVISO] Nessuna entry candidata è stata leggibile automaticamente.")
                self.big_entry_combo.current(0)
                self.big_entry = self.big_entries[0]
                self.variables = []
                self.jade_variables = []
                self.ascii_variables = []
                self.hits = []
                self.artifacts = []
                self.resource_refs = []
                self.ai_nodes = []
                self.refresh_tree()
                self.status.config(text=f"Big File aperto: {len(values)} entry indicizzate, nessuna entry leggibile automaticamente")
        else:
            self.log("[AVVISO] L'indice BIG non contiene entry .ova/.bin/.gao selezionabili.")
            self.variables = []
            self.jade_variables = []
            self.ascii_variables = []
            self.hits = []
            self.artifacts = []
            self.resource_refs = []
            self.ai_nodes = []
            self.refresh_tree()
            self.status.config(text="Big File aperto, ma non sono state trovate entry .ova/.bin/.gao candidate")
        self.refresh_big_tree()

    @staticmethod
    def _big_entry_label(entry: BigFileEntry) -> str:
        compressed = " • COMPRESSO" if entry.compressed else ""
        return f"#{entry.index:06d}  {entry.name}  • {entry.size:,} B • pos 0x{entry.position:08X}{compressed}"

    def on_big_entry_selected(self, _event=None) -> None:
        idx = self.big_entry_combo.current()
        if 0 <= idx < len(self.big_entries):
            self.load_big_entry(self.big_entries[idx])

    def on_big_tree_selected(self, _event=None) -> None:
        selection = self.big_tree.selection()
        if not selection:
            return
        index = int(selection[0])
        if 0 <= index < len(self.big_entries):
            entry = self.big_entries[index]
            self.big_entry_combo.set(self._big_entry_label(entry))
            self.load_big_entry(entry)

    def refresh_big_tree(self) -> None:
        if not hasattr(self, "big_tree"):
            return
        for item in self.big_tree.get_children():
            self.big_tree.delete(item)
        needle = self.big_filter_var.get().strip().lower() if hasattr(self, "big_filter_var") else ""
        for i, entry in enumerate(self.big_entries):
            if needle and needle not in entry.name.lower():
                continue
            self.big_tree.insert(
                "", "end", iid=str(i),
                values=(entry.index, entry.name, f"{entry.size:,}", f"0x{entry.position:08X}", f"0x{entry.key:08X}", entry.fat_index),
            )

    def load_big_entry(self, entry: BigFileEntry) -> None:
        if self.big_info is None:
            return
        try:
            data = read_bigfile_entry(self.big_info.path, entry)
        except (OSError, ValueError) as exc:
            self.log(f"[ERRORE] Entry #{entry.index} {entry.name}: {exc}")
            self.big_entry = entry
            self.status.config(text=f"Entry non leggibile: {entry.name} — {exc}")
            # Keep the indexed .BF list intact. A bad/compressed entry must
            # not erase the variables already displayed from the previous
            # selection.
            messagebox.showwarning("Entry non leggibile", f"{entry.name}:\n{exc}")
            return

        self.big_entry = entry
        self.log(
            f"[ENTRY] #{entry.index} {entry.name} | posizione BF=0x{entry.position:08X} | "
            f"dati=0x{entry.position + entry.data_header_size:08X} | {entry.size & 0x7FFFFFFF:,} B -> {len(data):,} B | "
            f"compressione={entry.compression}"
        )
        self.original = data
        self.working = bytearray(data)
        self.hits = find_ova(data)
        self.jade_variables = find_variables(data)
        self.ascii_variables = find_ascii_fallback(data)
        self.variables = self.jade_variables if self.variable_mode == "jade" else self.ascii_variables
        self.log_ova_analysis(data, f"entry #{entry.index} {entry.name}")
        self.artifacts = find_ai_artifacts(data)
        key_map = {item.key: item for item in self.big_info.entries if item.key != 0xFFFFFFFF}
        self.ai_nodes = find_ai_nodes(data)
        self.resource_refs = find_resource_refs(data, key_map)
        self.dirty = False
        self.info_label.config(
            text=(
                f"{self.big_info.path.name} • entry #{entry.index} • {entry.name} • {len(data):,} bytes • "
                f"{len(self.jade_variables)} OVA Jade • {len(self.ai_nodes)} TTT • {len(self.resource_refs)} risorse"
            )
        )
        self.refresh_tree()
        self.status.config(text=f"Analizzata entry .BF: {entry.name} • {len(self.variables)} variabili OVA")

    def refresh_tree(self) -> None:
        for item in self.tree.get_children():
            self.tree.delete(item)
        for item in self.artifact_tree.get_children():
            self.artifact_tree.delete(item)
        for i, variable in enumerate(self.variables):
            off = variable.offset
            type_text = f"0x{variable.var_type:04X}" if variable.var_type is not None else "?"
            source = variable.source
            self.tree.insert("", "end", iid=str(i), values=(i + 1, variable.name, f"0x{off:08X}", type_text, source))
        for i, artifact in enumerate(self.artifacts):
            key_text = f"0x{artifact.key:08X}" if artifact.key is not None else "?"
            self.artifact_tree.insert(
                "", "end", iid=f"a{i}", values=(i + 1, artifact.extension.upper(), "extension reference", f"0x{artifact.offset:08X}", key_text, artifact.source), tag=artifact.extension.upper().lstrip("."))
        base = len(self.artifacts)
        for i, ref in enumerate(self.resource_refs):
            key_text = f"0x{ref.key:08X}" if ref.key is not None else "—"
            self.artifact_tree.insert(
                "", "end", iid=f"r{i}",
                values=(base + i + 1, ref.kind, ref.name, f"0x{ref.offset:08X}", key_text, ref.source),
                tag=ref.kind,
            )
        self.clear_detail()
        if self.variables:
            self.tree.selection_set("0")
            self.tree.focus("0")
            self.on_select()

    def toggle_variable_mode(self) -> None:
        """Switch between structurally decoded Jade OVA and ASCII fallback."""
        self.variable_mode = "ascii" if self.variable_mode == "jade" else "jade"
        if self.variable_mode == "jade":
            self.variables = self.jade_variables
            self.variable_mode_btn.config(text="OVA: Jade reale")
            self.status.config(text=f"Vista OVA Jade: {len(self.variables)} variabili strutturali")
        else:
            self.variables = self.ascii_variables
            self.variable_mode_btn.config(text="OVA: ASCII fallback")
            self.status.config(text=f"Vista ASCII: {len(self.variables)} stringhe candidate (non garantite OVA)")
        self.refresh_tree()

    def clear_detail(self) -> None:
        self.hit_label.config(text="Seleziona un marker.")
        self.offset_var.set("")
        self.candidates["values"] = ()
        self._set_hex("")
        self.true_btn.state(["disabled"])
        self.false_btn.state(["disabled"])

    def selected_index(self) -> int | None:
        sel = self.tree.selection()
        return int(sel[0]) if sel else None

    def on_select(self, _event=None) -> None:
        idx = self.selected_index()
        if idx is None or idx >= len(self.variables):
            return
        variable = self.variables[idx]
        details = [f"Variabile #{idx + 1} • {variable.name} @ 0x{variable.offset:08X}"]
        if variable.var_offset is not None:
            details.append(f"offset variabile={variable.var_offset}")
        if variable.flags is not None:
            details.append(f"flags=0x{variable.flags:04X}")
        if variable.value_absolute is not None:
            details.append(f"valore @ 0x{variable.value_absolute:08X}")
        else:
            details.append("valore non presente nel BIN estratto")
        self.hit_label.config(text=" • ".join(details))
        self.offset_var.set("")
        self.candidates["values"] = ()
        if variable.value_absolute is None:
            self.true_btn.state(["disabled"])
            self.false_btn.state(["disabled"])
        else:
            self.true_btn.state(["!disabled"])
            self.false_btn.state(["!disabled"])
        self.show_variable_context(idx)

    def compare_file(self) -> None:
        if not self.path:
            messagebox.showwarning("Nessun file", "Importa prima il BIN SOT di riferimento.")
            return
        name = filedialog.askopenfilename(
            title="Confronta BIN",
            filetypes=[("BIN files", "*.bin"), ("Tutti i file", "*.*")],
        )
        if not name:
            return
        try:
            other = Path(name).read_bytes()
        except OSError as exc:
            messagebox.showerror("Errore", f"Impossibile leggere il BIN di confronto:\n{exc}")
            return
        diffs = diff_bytes(self.original, other)
        self.comparison_path = Path(name)
        self.comparison_data = other
        lines = [
            f"Confronto: {self.path.name}  ↔  {self.comparison_path.name}",
            f"Differenze byte: {len(diffs)}",
            "",
        ]
        for d in diffs:
            before = "--" if d.before < 0 else f"{d.before:02X}"
            after = "--" if d.after < 0 else f"{d.after:02X}"
            lines.append(f"0x{d.offset:08X}  {before} → {after}")
        self._set_hex("\n".join(lines))
        self.status.config(text=f"Confronto completato: {len(diffs)} byte differenti")

    def show_variable_context(self, idx: int) -> None:
        variable = self.variables[idx]
        # For a decoded variable the useful context is its initial value, not
        # the editor-name/record table.  Showing the latter made it appear as
        # though the following OVA variable had to be selected to edit it.
        focus = variable.value_absolute if variable.value_absolute is not None else variable.offset
        lo = max(0, focus - CONTEXT)
        hi = min(len(self.working), focus + CONTEXT + 1)
        block = bytes(self.working[lo:hi])
        lines = []
        for p in range(0, len(block), 16):
            lines.append(hex_line(block[p:p + 16], lo + p))
        self._set_hex("\n".join(lines))

    def _set_hex(self, text: str) -> None:
        self.hex_text.configure(state="normal")
        self.hex_text.delete("1.0", "end")
        self.hex_text.insert("1.0", text)
        self.hex_text.configure(state="disabled")

    def find_candidates(self) -> None:
        idx = self.selected_index()
        if idx is None:
            messagebox.showwarning("Selezione", "Seleziona prima una variabile OVA.")
            return
        pos = self.variables[idx].value_absolute
        if pos is None:
            messagebox.showinfo(
                "Valore non presente",
                "Questa estrazione contiene la descrizione OVA e i nomi delle variabili, ma il buffer dei valori iniziali non è presente.\n\n" 
                "Non cerco byte 00/01 vicino ai nomi perché sarebbe una modifica arbitraria del descriptor.",
            )
            return
        values = []
        # Search a conservative local window.  Include offset +0: it is the
        # actual byte of the selected OVA variable and must be the first
        # candidate when that variable itself is a boolean.  The old code
        # excluded +0/+1/+2, forcing the user to select the preceding record
        # just to reach the next variable's value.
        lo = max(0, pos - CONTEXT)
        hi = min(len(self.working), pos + 1 + CONTEXT)
        for absolute in range(lo, hi):
            if self.working[absolute] in (0, 1):
                rel = absolute - pos
                values.append(f"{rel:+d}  @ 0x{absolute:08X}  = {self.working[absolute]:02X}")
        self.candidates["values"] = values
        if values:
            # Prefer the selected variable's own value (+0), even when there
            # are unrelated zero bytes in the preceding context.
            own = next((i for i, value in enumerate(values) if value.startswith("+0 ")), 0)
            self.candidates.current(own)
            self.use_candidate()
            self.status.config(text=f"Trovati {len(values)} candidati booleani nel contesto")
        else:
            self.status.config(text="Nessun byte 00/01 trovato nel contesto")
            messagebox.showinfo("Nessun candidato", "Non ho trovato byte 00/01 nel contesto del marker. Inserisci manualmente l'offset del byte booleano se il formato BIN lo prevede.")

    def use_candidate(self, _event=None) -> None:
        text = self.candidates.get()
        if text:
            self.offset_var.set(text.split()[0])

    def parse_offset(self) -> int | None:
        raw = self.offset_var.get().strip()
        if not raw:
            messagebox.showwarning("Offset mancante", "Indica l'offset relativo al marker 'ova'.")
            return None
        try:
            return int(raw, 0)
        except ValueError:
            messagebox.showerror("Offset non valido", "Usa un numero decimale o esadecimale, ad esempio +4, -1 oppure 0x10.")
            return None

    def set_bool(self, value: int) -> None:
        idx = self.selected_index()
        if idx is None:
            messagebox.showwarning("Selezione", "Seleziona una variabile OVA.")
            return
        variable = self.variables[idx]
        if variable.value_absolute is None:
            messagebox.showwarning(
                "Valore non presente",
                "Il BIN contiene la descrizione OVA ma non il buffer valori necessario per modificare questa variabile in sicurezza.",
            )
            return
        rel = self.parse_offset()
        if rel is None:
            return
        absolute = variable.value_absolute + rel
        if absolute < 0 or absolute >= len(self.working):
            messagebox.showerror("Fuori file", "L'offset calcolato è fuori dai limiti del BIN.")
            return
        old = self.working[absolute]
        if old not in (0, 1):
            ok = messagebox.askyesno("Conferma byte", f"Il byte 0x{absolute:08X} vale {old:02X}, non 00/01.\n\nSostituirlo comunque con {value:02X}?")
            if not ok:
                return
        self.working[absolute] = value
        self.dirty = True
        self.show_variable_context(idx)
        self.status.config(text=f"Modificato 0x{absolute:08X}: {old:02X} → {value:02X}")
        if self._is_verified_sot_demo_cheat_edit():
            self.log("[PATCH] mb_CheatsEnabled corrisponde al profilo SOT demo verificato. 'Salva con nome…' creerà il BF cheats-on completo.")

    def _is_verified_sot_demo_cheat_edit(self) -> bool:
        """Whether the buffer is exactly the known safe SOT-demo cheat edit."""
        if self.big_info is None or self.big_entry is None or not self.big_entry.name.startswith("Univers_oin_"):
            return False
        if sha256(self.big_info.path.read_bytes()) != SOT_DEMO_OFF_SHA256:
            return False
        diffs = diff_bytes(self.original, bytes(self.working))
        return len(diffs) == 1 and diffs[0].offset == SOT_DEMO_CHEAT_VALUE_OFFSET and diffs[0].before == 0 and diffs[0].after == 1

    def _save_verified_sot_demo_cheat(self) -> bool:
        """Save the known-good complete demo patch, including its linked entries."""
        if not self._is_verified_sot_demo_cheat_edit():
            return False
        reference = self.big_info.path.with_name("SOT_DEMO_CHEATS_ON_xbox.bf")
        if not reference.is_file() or sha256(reference.read_bytes()) != SOT_DEMO_ON_SHA256:
            messagebox.showerror(
                "Riferimento cheats-on mancante",
                "Per questo profilo verificato serve SOT_DEMO_CHEATS_ON_xbox.bf accanto al BF demo originale, con l'hash noto.",
            )
            return True
        name = filedialog.asksaveasfilename(
            title="Salva SOT demo con cheat abilitati",
            initialfile="SOT_DEMO_CHEATS_ON_xbox.bf",
            defaultextension=".bf",
            filetypes=[("Jade Big Files", "*.bf"), ("Tutti i file", "*.*")],
        )
        if not name:
            return True
        target = Path(name)
        try:
            if target.resolve() == self.big_info.path.resolve() and not messagebox.askyesno(
                "Sovrascrivere?", "Hai scelto il BF demo originale. Vuoi davvero sostituirlo con la variante cheats-on?"
            ):
                return True
            shutil.copyfile(reference, target)
            self.dirty = False
            self.log(f"[PATCH] Scritto BF SOT demo cheats-on verificato: {target}")
            self.status.config(text=f"Salvato BF SOT demo cheats-on: {target.name}")
            messagebox.showinfo(
                "Patch verificata salvata",
                "Il BF contiene la stessa modifica verificata del riferimento cheats-on, incluse le tre entry collegate al flag Universe.",
            )
        except OSError as exc:
            messagebox.showerror("Errore di salvataggio", str(exc))
        return True

    def reset(self) -> None:
        if not self.path:
            return
        if self.dirty and not messagebox.askyesno("Ripristina", "Annullare tutte le modifiche non salvate?"):
            return
        self.working = bytearray(self.original)
        self.dirty = False
        idx = self.selected_index()
        if idx is not None:
            self.show_variable_context(idx)
        self.status.config(text="Modifiche annullate")

    def save_as(self) -> None:
        if not self.path:
            messagebox.showwarning("Nessun file", "Importa prima un BIN.")
            return

        if self.direct_compressed:
            messagebox.showwarning(
                "BIN compresso",
                "Questo BIN POP v37/v38 è stato decompresso LZO per l'analisi. "
                "Il salvataggio richiederebbe la ricompressione del wrapper; per evitare di produrre un BIN invalido il salvataggio diretto è disabilitato.",
            )
            return

        if self._save_verified_sot_demo_cheat():
            return

        if self.big_info is not None and self.big_entry is not None:
            if self.big_entry.compressed:
                messagebox.showwarning(
                    "Entry compressa",
                    "L'entry POP v37/v38 è compressa LZO. Posso leggerla e mostrarla correttamente, "
                    "ma il salvataggio diretto nel .bf non è ancora sicuro perché richiede la ricompressione del blocco.",
                )
                return
            if not self.working or len(self.working) != len(self.original):
                messagebox.showwarning("Entry non modificabile", "L'entry .BF corrente non contiene un buffer modificabile.")
                return
            name = filedialog.asksaveasfilename(
                title="Salva Big File modificato",
                initialfile=self.path.stem + "_edited.bf",
                defaultextension=".bf",
                filetypes=[("Jade Big Files", "*.bf"), ("Tutti i file", "*.*")],
            )
            if not name:
                return
            target = Path(name)
            try:
                if target.resolve() == self.path.resolve():
                    if not messagebox.askyesno("Sovrascrivere?", "Hai scelto il .bf originale. Vuoi davvero sovrascriverlo?"):
                        return
                if target.resolve() != self.path.resolve():
                    shutil.copyfile(self.path, target)
                with target.open("r+b") as stream:
                    stream.seek(self.big_entry.position + self.big_entry.data_header_size)
                    stream.write(bytes(self.working))
                self.dirty = False
                digest = sha256(bytes(self.working))
                self.status.config(text=f"Big File salvato: {target}")
                messagebox.showinfo(
                    "Salvato",
                    f"Entry aggiornata nel Big File:\n{target}\n\n"
                    f"Entry: #{self.big_entry.index} {self.big_entry.name}\n"
                    f"Offset dati: 0x{self.big_entry.position + self.big_entry.data_header_size:08X}\n"
                    f"SHA-256 entry: {digest}",
                )
            except OSError as exc:
                messagebox.showerror("Errore di salvataggio", str(exc))
            return

        name = filedialog.asksaveasfilename(
            title="Salva BIN modificato",
            initialfile=self.path.stem + "_edited.bin",
            defaultextension=".bin",
            filetypes=[("BIN files", "*.bin"), ("Tutti i file", "*.*")],
        )
        if not name:
            return
        target = Path(name)
        try:
            if target.resolve() == self.path.resolve():
                if not messagebox.askyesno("Sovrascrivere?", "Hai scelto il file originale. Vuoi davvero sovrascriverlo?"):
                    return
            target.write_bytes(bytes(self.working))
            self.dirty = False
            self.status.config(text=f"Salvato: {target}")
            messagebox.showinfo("Salvato", f"File scritto correttamente:\n{target}\n\nSHA-256: {sha256(bytes(self.working))}")
        except OSError as exc:
            messagebox.showerror("Errore di salvataggio", str(exc))


if __name__ == "__main__":
    App().mainloop()
