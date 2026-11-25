DATRA IMPLEMENTATION FOOTPRINT

Requirements: Python 3.9+ (with timezone data) and Git. No pip/npm installation.

From the repository root:
  python3 tools/loc-dashboard/serve.py

Or pass a different checkout explicitly:
  python3 tools/loc-dashboard/serve.py --repo /path/to/datra

Then open http://127.0.0.1:8765 in your browser. Keep the helper running.
Press Ctrl+C in its terminal to stop it. Use --port 8766 if needed.

WHAT IT DOES
- Reads the checkout's currently selected branch and committed HEAD.
- Automatically rebuilds after commits, branch changes, or a new calendar day.
- Draws total physical LOC and trailing seven-calendar-day net growth.
- Excludes datra-haskell/docs/, datra-haskell/src/DatraCore/, and
  datra-haskell/test/ (including fixtures).
- Expands GitHub squash PRs whose commit subjects end with (#number), using
  original PR commits. Direct commits and merge adjustments use committer dates;
  original PR commits use author dates, in America/New_York by default.
- Includes unmerged work when it is committed on the selected branch. It does not
  include uncommitted edits or hypothetical future merges.
- Uses no external chart scripts, fonts, or analytics. There are no event annotations.
- Checks the final calculated total against the selected commit's tree.

The HTML alone cannot read a local Git repository. Opening index.html directly
shows launch instructions. Serve it with the included helper for live data.

GIT ACCESS AND CACHING
The helper never checks out branches or edits your working tree/index. It creates
an isolated bare Git cache under your system temporary directory, and fetches
the selected local HEAD into that cache. For a github.com origin, it also fetches
original pull-request head refs using your existing Git authentication. The first
run can take longer and requires network access for complete squash histories.
No interactive authentication prompt is started by the helper.

If PR retrieval is unavailable, cached PR refs are used. Missing PRs are reported
on the page; those changes stay on merge dates instead of being invented. The final
total remains exact even when daily PR attribution is incomplete.

Options:
  --repo PATH          Git checkout (default: current directory)
  --port NUMBER        Local HTTP port (default: 8765)
  --timezone ZONE      Calendar timezone (default: America/New_York)
  --cache-dir PATH     Choose a persistent cache location
  --offline           Skip GitHub fetches; use local/cached history

Only a loopback HTTP server is started (127.0.0.1). It exposes this page and the
calculated metrics, not a general file browser or command-execution endpoint.
Keep this tool local; it is not designed as an internet-facing server.

COUNTING DETAILS
Physical lines include blank lines and comments, plus build/configuration and
root text files outside the excluded directories. Binary files and symlinks do
not count. A final nonempty line without a newline counts as one line.
Days without changes carry the previous total forward through the current day.
The first six days have no seven-day rate. The daily reconstruction combines
concurrent branch contributions; it is not a literal historical master checkout.

TESTS
From the repository root:
  python3 -m unittest discover -s tools/loc-dashboard -p 'test_*.py' -v

The tests create temporary Git repositories; they need no GitHub connection.
