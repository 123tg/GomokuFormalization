$ErrorActionPreference = 'Stop'

$cppRoot = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$solver = Join-Path $cppRoot 'build\solve_small_draws.exe'

if (-not (Test-Path -LiteralPath $solver)) {
  throw "missing solver executable: $solver"
}

function Invoke-CheckedSolve {
  param(
    [string[]]$Arguments,
    [string[]]$RequiredPatterns
  )

  $output = & $solver @Arguments 2>&1 | Out-String
  if ($LASTEXITCODE -ne 0) {
    throw "solver failed for arguments: $($Arguments -join ' ')`n$output"
  }
  foreach ($pattern in $RequiredPatterns) {
    if ($output -notmatch [regex]::Escape($pattern)) {
      throw "missing '$pattern' for arguments: $($Arguments -join ' ')`n$output"
    }
  }
  Write-Output "passed: $($Arguments -join ' ')"
}

Invoke-CheckedSolve `
  -Arguments @('--board', '5', '--pair-branches', '0', '--static-only') `
  -RequiredPatterns @('self_check=passed', 'result_for_black=draw')

Invoke-CheckedSolve `
  -Arguments @('--board', '6', '--pair-branches', '2') `
  -RequiredPatterns @(
    'self_check=passed',
    'reply_pairing_status=found',
    'proved_opening_orbits=6',
    'result_for_black=draw'
  )

Invoke-CheckedSolve `
  -Arguments @(
    '--board', '7',
    '--pair-branches', '2',
    '--pairing-nodes', '300',
    '--reply-probes', '8',
    '--reply-probe-nodes', '20',
    '--reply-probe-min-stones', '5',
    '--skip-reply-pairing',
    '--search-depth', '8',
    '--search-nodes', '100000',
    '--table-power', '20'
  ) `
  -RequiredPatterns @(
    'self_check=passed',
    'tree_value=breaker_win',
    'tree_node_budget_exhausted=false',
    'result_for_black=draw'
  )

Invoke-CheckedSolve `
  -Arguments @(
    '--board', '8',
    '--pair-branches', '2',
    '--pairing-nodes', '300',
    '--static-only'
  ) `
  -RequiredPatterns @('self_check=passed', 'static_pairing_status=node_limit')
