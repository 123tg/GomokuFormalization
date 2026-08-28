param(
  [switch]$Clean
)

$ErrorActionPreference = 'Stop'
$cppRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$buildDir = Join-Path $cppRoot 'build'
$cppRootFull = [System.IO.Path]::GetFullPath($cppRoot)
$buildDirFull = [System.IO.Path]::GetFullPath($buildDir)

if (-not $buildDirFull.StartsWith(
    $cppRootFull + [System.IO.Path]::DirectorySeparatorChar)) {
  throw 'build directory resolved outside cpp root'
}

if ($Clean -and (Test-Path -LiteralPath $buildDirFull)) {
  Remove-Item -LiteralPath $buildDirFull -Recurse -Force
}

New-Item -ItemType Directory -Path $buildDirFull -Force | Out-Null

$common = @(
  '-std=c++17', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Wpedantic',
  '-I', (Join-Path $cppRoot 'include'),
  (Join-Path $cppRoot 'src\gomoku_solver.cpp')
)

& g++ @common (Join-Path $cppRoot 'src\main.cpp') '-o' (Join-Path $buildDirFull 'gomoku_solver.exe')
if ($LASTEXITCODE -ne 0) {
  throw 'failed to build gomoku_solver.exe'
}

& g++ @common (Join-Path $cppRoot 'tests\solver_tests.cpp') '-o' (Join-Path $buildDirFull 'gomoku_tests.exe')
if ($LASTEXITCODE -ne 0) {
  throw 'failed to build gomoku_tests.exe'
}

$fullSolve = @(
  '-std=c++20', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Wpedantic',
  (Join-Path $cppRoot 'tools\solve5x5.cpp')
)

& g++ @fullSolve '-o' (Join-Path $buildDirFull 'solve5x5.exe')
if ($LASTEXITCODE -ne 0) {
  throw 'failed to build solve5x5.exe'
}

$smallDrawSolve = @(
  '-std=c++20', '-O3', '-DNDEBUG', '-Wall', '-Wextra', '-Wpedantic',
  (Join-Path $cppRoot 'tools\solve_small_draws.cpp')
)

& g++ @smallDrawSolve '-o' (Join-Path $buildDirFull 'solve_small_draws.exe')
if ($LASTEXITCODE -ne 0) {
  throw 'failed to build solve_small_draws.exe'
}

Write-Output "Built $buildDirFull\gomoku_solver.exe"
Write-Output "Built $buildDirFull\gomoku_tests.exe"
Write-Output "Built $buildDirFull\solve5x5.exe"
Write-Output "Built $buildDirFull\solve_small_draws.exe"
