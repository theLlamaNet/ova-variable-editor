param(
    [Parameter(Mandatory = $true)] [string] $InputFile,
    [Parameter(Mandatory = $true)] [string] $OutputFile,
    [Parameter(Mandatory = $true)] [ValidateSet('compress')] [string] $Mode,
    [string] $LzoDll = 'C:\Users\Admin\Desktop\Giochi\PopTools\bf_repacker_2018_05_23_1419\lzo.dll'
)

$ErrorActionPreference = 'Stop'

$source = @'
using System;
using System.Runtime.InteropServices;

public static class PopLzoNative
{
    [DllImport(@"C:\Users\Admin\Desktop\Giochi\PopTools\bf_repacker_2018_05_23_1419\lzo.dll")]
    public static extern int __lzo_init3();

    [DllImport(@"C:\Users\Admin\Desktop\Giochi\PopTools\bf_repacker_2018_05_23_1419\lzo.dll")]
    public static extern int lzo1x_1_compress(
        byte[] src,
        int src_len,
        byte[] dst,
        ref int dst_len,
        byte[] wrkmem);
}
'@

if (-not ('PopLzoNative' -as [type])) {
    Add-Type -TypeDefinition $source
}

$init = [PopLzoNative]::__lzo_init3()
if ($init -ne 0) {
    throw "LZO initialization failed (rc=$init)."
}

if ($Mode -ne 'compress') {
    throw "Unsupported mode: $Mode"
}

$input = [IO.File]::ReadAllBytes($InputFile)
if ($input.Length -lt 8) {
    throw 'Input is too short for a POP-LZO stream.'
}

$magic = [BitConverter]::ToString($input, 4, 4).Replace('-', '')
if ($magic -ne '99C0FFEE') {
    throw ('Input does not contain POP magic 99C0FFEE at offset 4 (found {0}).' -f $magic)
}

$blockSize = 131072
$result = New-Object IO.MemoryStream
$position = 0
while ($position -lt $input.Length) {
    $count = [Math]::Min($blockSize, $input.Length - $position)
    $block = New-Object byte[] $count
    [Array]::Copy($input, $position, $block, 0, $count)

    $dst = New-Object byte[] ($count + [Math]::Floor($count / 64) + 64 + 8)
    $outLength = $dst.Length
    $work = New-Object byte[] 65536
    $rc = [PopLzoNative]::lzo1x_1_compress($block, $count, $dst, [ref] $outLength, $work)
    if ($rc -ne 0) {
        throw "LZO compression failed (rc=$rc, block=$count bytes)."
    }

    $result.Write([BitConverter]::GetBytes([int]$count), 0, 4)
    if ($outLength -gt $count) {
        $result.Write([BitConverter]::GetBytes([int]$count), 0, 4)
        $result.Write($block, 0, $block.Length)
    } else {
        $result.Write([BitConverter]::GetBytes([int]$outLength), 0, 4)
        $result.Write($dst, 0, $outLength)
    }
    $position += $count
}

# Match PopTools: make the 4-byte entry-size prefix land on a 2048-byte boundary.
$payloadLength = [int]$result.Length
if ((($payloadLength + 4) % 2048) -ne 0) {
    $diff = (([Math]::Floor($payloadLength / 2048) * 2048) + 2044) - $payloadLength
    if ($diff -gt 0) {
        $result.Write((New-Object byte[] $diff), 0, $diff)
    }
}

[IO.File]::WriteAllBytes($OutputFile, $result.ToArray())
