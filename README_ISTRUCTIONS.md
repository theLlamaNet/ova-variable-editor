# OVA Variable Editor

Desktop Python/Tkinter UI to import `.bf`, `.bin`, and `.ova` files, analyze OVA records and `.ova`/`.ofc` AI references, display a list of detected variable names, and explicitly replace a boolean byte with `00` (FALSE) or `01` (TRUE) when the value buffer is actually present.

## Launch

```text
python ova_variable_editor.py

```

On Windows, having Python 3 installed is sufficient; Tkinter is normally included in official Python distributions.

## How It Works

1. `Import .BF / .BIN` accepts both a BIN dump and a Jade `.bf` Big File.
2. The program first searches for the real OVA structure used by the Jade source code: `sizeR`, 12-byte engine record, 30-byte editor name table, and relative offset/type/flags. In retail PoP37/38 Big Files, the description may preserve engine records but not the editor name table; in that case, the records are still displayed as `POP37/38 OVA` with synthetic `OVA_###` labels, instead of being mistaken for random ASCII text.
Standalone `Univers_oin_*.bin` files from PoP37/38 are themselves wrapped in LZO blocks: the program decompresses them before analysis. In complete retail builds, the name region may be present but encrypted/obfuscated; even in that case, the OVA structure is preserved as `POP37/38 OVA` and ASCII fallback is not used.
3. The `.ova/.ofc References` tab lists every explicit reference to these extensions, including the preceding 32-bit `BIG_KEY` when present.
4. Selecting a variable displays 48 bytes before and 48 bytes after the name; when the OVA record is structurally decoded, offset, type, and variable flags are also shown.
5. The parser no longer considers the text `ova` or a random ASCII string as a variable. For a full OVA, it can also follow the layout up to `pc_BufferInit` and calculate the value address.
6. `Search 00/01 candidates` and the TRUE/FALSE buttons are enabled only when the value buffer is actually present in the BIN file. The name table is not modified to guess a value.
7. `Compare with BIN…` automatically compares two SOT dumps and shows all differing bytes, making the cheats OFF/ON transition visible without searching by hand.
8. `Save As…` creates the modified BIN file. The original file is not overwritten by default.

### Jade Big File `.bf` Support

The `.bf` support follows the format described in the Jade source files `Libraries/SDK/Sources/BIGfiles`: `BIG\0` header, FAT descriptor, `BIG_tdst_File` table (position + `BIG_KEY`), and extended table with length and 64-byte name. Multiple chained FATs via `ul_NextPosFat` are also supported, as in the real `Rayman4.bf`.

When importing a `.bf`, the program **does not extract the Big File to disk**: it directly indexes the FAT and displays in the `Entries in .BF` tab the OVA/BIN entries as well as `.gao` files, because in complete Big Files the OVA description block can be embedded inside GAO files. A text filter is available to quickly find a specific file. If a structurally decodable `Univers_oin_*.bin` exists, it is preferred; otherwise, the program can use a GAO containing the same OVA description.

Selecting an entry loads only that content using the position stored in the FAT. Jade saves a `ULONG` file length in front of the payload; the parser verifies that the read length matches the FAT before analyzing the content. This prevents treating the entire `.bf` as a single blob and allows working with very large Big Files.

The `Rayman4.bf` located in `BigFiles` was verified with 2 FATs and 161,694 indexed entries; `Univers.ova` is entry #69185 at `0x0877D8BD`, 32,328 bytes long, and contains 184 structurally decodable OVA variables. Other present Big Files are indexed in the same way. Duplicate OVA variables across GAO files are not concatenated: only one source entry is loaded at a time, avoiding duplicate items in the list.

`Save As…` on a `.bf` entry creates a copy of the Big File and replaces **only the selected entry payload**, keeping the file size unchanged. Entries marked as compressed are not modified automatically: the tool prefers to refuse editing rather than writing decompressed data into compressed format.

### SOT BIN Analysis

In the three provided SOT BINs, the OVA record contains a real name table: it is not just `ova` at `0x002C`. In `Univers_oin_ff0c008e_SOT_CHEATS_OFF.bin`, the detector identifies dozens of strings as candidates for variable names or metadata, including `mk_CheckPoint_CurKey`, `mk_Restart`, `mb_Cam_Invert_Rotation`, `mi_Tutorials`, `mi_E3_ChangeMapAfterDela`, `CamManagerLoad`, `NumActorDeath`, `FreeLook`, `mb_Neverh3`, `InMenuInGamed`, and `mb_DisplayUbiLogo`.

Some names in the BIN are interrupted by binary bytes, for example `heatsEnable`, `urrentWorldIndex`, and `E3_IntersticeContr`. The program displays what is actually decodable from the file and does not invent missing prefixes. This is important to avoid turning a simple hypothesis into a BIN modification.

### Important Note on BIN Format

The string `ova` is used as an **anchor for identification**, but the UI no longer treats it as the variable list. In the analyzed BINs, the `ova` sequence at `0x002C` is identical between OFF/ON files, so modifying it directly would corrupt the record instead of changing a variable.

The Jade source code confirms that `AI_tdst_VarInfo` serializes `i_Offset`, `i_NumElem`, `w_Type`, and `w_Flags` into 12 bytes; the editor name is 30 bytes long. The variable offset is relative to the OVA's `pc_BufferInit`, not automatically the offset of the name within the file. For this reason, the tool no longer confuses ASCII text with value position.

## Rayman 4: `Univers_oin_ff0c008e_RAYMAN4.bin`

This dump is the case that motivated the fix. The file does not contain the ASCII `.ova`/`.ofc` references seen in SOT dumps; instead, a portion of the Jade OVA description is directly present at `0x6A3`:

* `sizeR = 108` bytes → 9 12-byte `AI_tdst_VarInfo` records;
* `names_size = 270` bytes → 9 30-byte slots;
* records have offsets `0, 4, 8, 12, 16, 20, 24, 28, 32`;
* type IDs correspond to the Jade `AIdeftyp.h` table (`43=network`, `34=float`, `33=int`, `40=object`);
* the 2044-byte dump ends before the end of the 270-byte name table.

The program now recognizes **8 real OVA names** instead of the unrelated strings from the previous ASCII detector:

`Territory_Path`, `Att_Protect_Gao_Dist`, `Att_Protect_Gao_Vision`, `App_Item_Gao`, `Mort_SeReleve`, `Att_WAY`, `Item_Arme_Utilisable`, `Item_Rafale`.

The UI explicitly indicates `truncated: 8/9 names`: the ninth record is real in the descriptor, but its name slot is not contained in the available dump. This avoids inventing the missing name.

The same dump does not contain the complete `pc_BufferInit` after the name table, so variables are displayed and typed but are not made editable as simple boolean bytes. To modify the value, the full `.ova` or a dump including the initial buffer is required.

In the project's SOT dumps, `mb_EnableCheats` is not stored as a complete string: decodable text contains `heatsEnable` at `0x197`. The tool now preserves this distinction and does not invent missing prefixes. The `SOT_CHEATS_OFF`/`SOT_CHEATS_ON` comparison detects 17 differing bytes, all in the `0x316..0x32B` region (with some gaps), which is the concrete observable change between the two files.