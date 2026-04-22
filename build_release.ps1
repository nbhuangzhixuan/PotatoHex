$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$Root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $Root

function Invoke-PyInstaller {
    param(
        [string]$SpecName,
        [string]$DistPath,
        [string]$WorkPath
    )

    if (Test-Path -LiteralPath $DistPath) {
        Remove-Item -LiteralPath $DistPath -Recurse -Force
    }
    if (Test-Path -LiteralPath $WorkPath) {
        Remove-Item -LiteralPath $WorkPath -Recurse -Force
    }
    New-Item -ItemType Directory -Force -Path $DistPath, $WorkPath | Out-Null

    & python -m PyInstaller --noconfirm --clean --distpath $DistPath --workpath $WorkPath $SpecName
    if ($LASTEXITCODE -ne 0) {
        throw "PyInstaller failed: $SpecName"
    }
}

function Copy-Tree {
    param(
        [string]$Source,
        [string]$Destination
    )

    if (-not (Test-Path -LiteralPath $Source)) {
        throw "Missing output directory: $Source"
    }
    New-Item -ItemType Directory -Force -Path $Destination | Out-Null
    Copy-Item -Path (Join-Path $Source "*") -Destination $Destination -Recurse -Force
}

function Copy-FileIfExists {
    param(
        [string]$Source,
        [string]$Destination
    )

    if (Test-Path -LiteralPath $Source) {
        Copy-Item -LiteralPath $Source -Destination $Destination -Force
    }
}

$TempRoot = Join-Path $Root "build_release_tmp"
$LauncherDist = Join-Path $TempRoot "launcher_dist"
$LauncherWork = Join-Path $TempRoot "launcher_work"
$MainDist = Join-Path $TempRoot "main_dist"
$MainWork = Join-Path $TempRoot "main_work"
$ReleaseRoot = Join-Path $Root "release"
$ReleaseStage = Join-Path $TempRoot "release_stage"

if (Test-Path -LiteralPath $TempRoot) {
    Remove-Item -LiteralPath $TempRoot -Recurse -Force
}
if (Test-Path -LiteralPath $ReleaseRoot) {
    try {
        Remove-Item -LiteralPath $ReleaseRoot -Recurse -Force
    } catch {
        Write-Host "[Warn] release folder is locked; using existing folder."
    }
}
New-Item -ItemType Directory -Force -Path $TempRoot | Out-Null

Invoke-PyInstaller -SpecName "launcher.spec" -DistPath $LauncherDist -WorkPath $LauncherWork
Invoke-PyInstaller -SpecName "main.spec" -DistPath $MainDist -WorkPath $MainWork

if (Test-Path -LiteralPath $ReleaseStage) {
    Remove-Item -LiteralPath $ReleaseStage -Recurse -Force
}
New-Item -ItemType Directory -Force -Path $ReleaseStage | Out-Null
Copy-Item -Path (Join-Path $LauncherDist "launcher\*") -Destination $ReleaseStage -Recurse -Force
Copy-Item -Path (Join-Path $MainDist "main\*") -Destination $ReleaseStage -Recurse -Force

if (-not (Test-Path -LiteralPath $ReleaseRoot)) {
    New-Item -ItemType Directory -Force -Path $ReleaseRoot | Out-Null
}
Copy-Item -Path (Join-Path $ReleaseStage "*") -Destination $ReleaseRoot -Recurse -Force

Copy-FileIfExists -Source (Join-Path $Root "requirements.txt") -Destination $ReleaseRoot
Copy-FileIfExists -Source (Join-Path $Root "hextech_reco_cache.json") -Destination $ReleaseRoot
Copy-FileIfExists -Source (Join-Path $Root "hextech_augment_index.json") -Destination $ReleaseRoot
Copy-FileIfExists -Source (Join-Path $Root "hextech_reco_cache.json") -Destination $ReleaseRoot
Copy-FileIfExists -Source (Join-Path $Root "hextech_augment_index.json") -Destination $ReleaseRoot

Write-Host ""
Write-Host "Build complete. Release folder: $ReleaseRoot"
Write-Host "It contains launcher.exe and main.exe in the same folder."
