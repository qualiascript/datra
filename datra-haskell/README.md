# datra-haskell

The Datra parser and interpreter are built with:

- GHC 9.14.1
- cabal-install 3.18.1.0
- Z3 (the SMT solver used by Liquid Haskell)

The ordinary `cabal.project` selects the repository-scoped GHC installation.
Both Docker targets use `cabal.docker.project` instead, which selects the pinned
compiler and Cabal executable from the container. This prevents a host Cabal
or the repository-relative `../.tools` paths from affecting container builds.

## Download and install the latest production image

To run Datra without compiling it, use the prebuilt release image. You need
Docker and curl; you do not need a repository checkout or a Haskell toolchain.

[Download the latest production image](https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz)
or run:

```sh
mkdir -p dist
curl --fail --location \
  https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz \
  --output dist/datra-prod.tar.gz && \
  sudo docker image load --input dist/datra-prod.tar.gz
```

This loads `datra-haskell:prod` into your local Docker image store. Continue
with [Run the whole pipeline](#run-the-whole-pipeline) below. If your account
can access Docker directly, omit `sudo`; otherwise use `sudo docker` in the
run commands too. Check the release notes for the supported platform.

The latest release must contain an asset named exactly `datra-prod.tar.gz`.
Publish each new production image under that same asset filename so this
link continues to work. The `&&` runs the Docker load only if the download
succeeds. Repeat these commands to install a newer release.

## Build development and production images

The images have separate targets and tags:

| Target | Image tag | Purpose |
| --- | --- | --- |
| `development` | `datra-haskell:development` | Full toolchain for building, testing, and interactive development |
| `prod` (default) | `datra-haskell:prod` | Slim runtime for running the Datra CLI |

From this directory, build both images:

```sh
make docker-images
```

Or build them individually with Docker:

```sh
docker build --target development --tag datra-haskell:development .
docker build --target prod --tag datra-haskell:prod .
```

The equivalent Make targets are `make docker-development` and
`make docker-prod`. Production is the default Docker stage and the default
Make target. Use the explicit tags above to keep the two images separate.

The multi-stage build verifies the toolchain and SMT solver, builds the
executable with the Liquid Haskell flag enabled, and strips the executable.
The default image uses Debian Bookworm slim and contains only Datra, its system
runtime libraries, and license notices. GHC, Cabal, Z3, sources, and build caches
stay in the build stage. CLI smoke tests run in the final runtime image. The
image supports Docker's `amd64` and `arm64` platforms.

This reduces the size of the image you distribute and download. A first build
from source still downloads the Haskell toolchain and compiles dependencies
with Liquid Haskell verification; subsequent builds reuse Docker's cached
dependency layer when the package metadata is unchanged. Build once and push
the resulting runtime image to your registry to let other machines pull it
without compiling it themselves.

Compare the local image sizes (in bytes):

```sh
docker image inspect datra-haskell:development datra-haskell:prod \
  --format '{{join .RepoTags ", "}}: {{.Size}} bytes'
```

## Run the whole pipeline

The `build` command parses and interprets Datra source. After downloading or building the
production image, run the whole pipeline and print only the final result:

```sh
docker run --rm datra-haskell:prod build \
  --source '(1; 2 + 3)' \
  --output -
```

The `--output -` option
prints the interpreted result to the terminal:

```text
(1; 5)
```

### Also display the AST

Use `--ast-output -` to print the AST before the final result:

```sh
docker run --rm datra-haskell:prod build \
  --source '(1; 2 + 3)' \
  --ast-output - \
  --output -
```

Expected output:

```text
(<:> 1 (+ 2 3))
(1; 5)
```

### Programs and begin/yield

Outer parentheses select expression mode: `(2 + 3)` produces `5`. Without
parentheses enclosing the entire resource, the file (or `--source` input) is
an implicit `begin`/`yield` block. A leading `begin` is optional. If `yield` is
omitted, the block uses `yield 0`; a bare `2 + 3` therefore produces `0`.
Comments and whitespace outside the enclosing parentheses do not change modes.

In a block, semicolons or newlines separate imported bindings:

```datra
a := 2 * 3
b := 5
yield a + b
```

This prints just `11`. Adding `begin` before `a` produces the same result.
From this directory, run it without Docker using a built executable:

```sh
./dist/datra-haskell build \
  --source 'a := 2 * 3
b := 5
yield a + b' \
  --ast-output /dev/null --output -
```

This command prints `11`. The `:=` spelling supplies a value directly.

Ordinary bindings remain unevaluated until referenced. `let` bindings are
evaluated before the block yields, even when unused. Both are visible throughout
the block and nested blocks, including before their declaration:

```datra
a : x + 1
let x : 10
yield a
```

This prints `11`. Names are local to the block, and nested blocks inherit the
outer scope. Reusing an identifier string already in that scope is an error;
unknown identifiers and cyclic references are errors too. Optional names,
`~>` / `<~` specification, and `of` subfederation work within blocks.

To retain an explicit block as the result's specification, enclose the entire
expression in parentheses:

```sh
./dist/datra-haskell build \
  --source '(begin
 a : 2 * 3
 b : 5
yield a + b)' \
  --ast-output /dev/null --output -
```

Output:

```datra
11 <~ begin
 a : 2 * 3
 b : 5
yield a + b
```

The retained block records how the result was evaluated; arithmetic and type
operations still use the resulting value. An implicit program prints only its
result, even when that result comes from a nested explicit block. Wrap expression
examples below in outer parentheses when running them as a whole file, or put
them after `yield` in a program. Typed `eval` continues to decode canonical data;
its input string is not treated as an implicit program.

### Argument maps

Braces admit every ordering of their arguments. For example, `{b := 8, 2}`
expands to the alternatives `(b := 8; 2) | (2; b := 8)`. Optional identifiers
such as `a? : Nat` accept either a named or an unnamed value; they do not make
the value itself optional.

```sh
docker run --rm datra-haskell:prod build \
  --source '({b : 8, 2} ~> {a? : Nat := 2, b? : Nat})' \
  --ast-output - \
  --output -
```

Specification checks every source ordering against the target, preserving
the supplied order and naming in the result:

```datra
{b : 8, 2} ~> {a? : Nat := 2, b? : Nat}
```

`b := 8` canonically renders as `b : 8`. Use `of` instead of `~>` to ask
whether the source is a subfederation of the target. Unknown names, incompatible
types, and missing required arguments are rejected. Both `;` and newlines
also separate arguments; canonical output uses commas when the pages are
total. Parentheses retain a nested map as one argument, as in `{(1, 2), 3}`.
Empty and unary braces reduce to `()` and their sole argument respectively.

Argument maps also compose with ordered concatenation. In
`x : 3, {b : 8, 2} ~> x : 3, {a? : Nat := 2, b? : Nat}`, the `x` component
stays in place while the brace-enclosed arguments may change order and omit
names. Specification checks every permitted source ordering and preserves
the written presentation. Reverse specification (`<~`) and subfederation
(`of`) use the same local argument-order boundaries.

Argument maps currently enumerate the finite permutations and distribute
optional-name alternatives, removing identical branches. Large argument
lists can therefore be expensive.

### Typed evaluation

`eval source at target` decodes canonical text against a target federation and
returns the captured value with its specification. Non-string targets use
the matching and extraction machinery of `%(source ~> "%(target)")[1]`
(where `source` and `target` stand for expressions). A string-template target
retains the whole matched string specification, so `%` can subsequently
extract all its captures.

```sh
./dist/datra-haskell build \
  --source '(eval "x : 3, (b : 8; 2)" at x : 3; {a? : Nat := 2, b? : Nat})' \
  --ast-output - \
  --output -
```

The `at` keyword separates the input expression from the target. Semicolons
and newlines after `at` belong to the target map, through the end of
the enclosing expression. Parenthesize `eval` when applying another operator
to its result:

```datra
(eval "(b : 8; 2)" at {a? : Nat, b? : Nat})[1] * 5
```

This produces `10`. Optional identifiers, specification, and subfederation
retain their ordinary semantics. Input must use canonical data spelling:
`eval "12" at Int` succeeds, while `eval "1 + 2" at Nat` is rejected.

`from`, `range`, and control forms are declared with AST patterns in
`standard_library.datra`. `$Int` captures an expression whose value is checked
when called; `%Int` remains string-template interpolation. These are separate
operations: AST patterns do not format and reparse an expression as text.
`if` retains its unevaluated branches and evaluates only the selected branch.

You can inspect the same template captures explicitly:

```datra
%(eval "from 2 to 5" at "from %Int to %Int")[1]
%(eval "from 2 to 5" at "from %Int to %Int")[2]
```

These produce `2 ~> Int` and `5 ~> Int` respectively.

### Functions, syntax patterns, and external symbols

`A -> B` is a function type. A typed `do` block supplies its implementation:

```datra
add := ({a? : Int, b? : Int} -> Int do yield a + b)
yield add (b : 5; 6)
```

The result is `11`. Application is written `f input` and binds before arithmetic.
Parenthesize a named domain, or use braces, to distinguish it from an identifier
whose annotation is itself a function type. Ordered pages retain their order;
argument-map segments admit permutations. Optional names are imported into the
body even when omitted by the caller. Ambiguous assignments are rejected.

An untyped block such as `add := (do yield a + b)` infers its unresolved numeric
parameters and captures existing lexical bindings. Inference is conservative:
unconstrained parameters and unsupported constraints require an explicit type.
Function specification checks input contravariance and output covariance;
`of` uses the same relation. Implementations are not tested on sample inputs to
establish their type.

Recursive functions use an explicit signature to check calls to themselves.
For example, this factorial function handles nonnegative inputs:

```datra
factorial := ({n? : Int} -> Int do
  yield if n = 0 then 1 else n * factorial (n - 1))
yield factorial 5
```

The output is `120`. `factorial 0` returns `1`; the lazy `if` leaves the
recursive branch unevaluated at the base case. The optional name also permits
`factorial (n : 5)`.

Registered Haskell implementations and primitive types use a symbol string:

```datra
add := external "datra.add"
yield add (b : 5; 6)
```

Unknown symbols are errors. External implementations are registered in the
executable; this syntax does not load arbitrary host code or shared libraries.

AST patterns attach surface syntax to a function. `as` accepts its pattern;
`as?` additionally permits ordinary application. Alternatives are explicit sum
values joined with `|`, in one declaration. Repeating a declaration is an error.
For example, `from` has a bounded alternative and a directional alternative:

```datra
_Wards := ($upwards | $downwards)
from := (
  ("$Int to $Int" as? (Int, Int -> IntRange) external "datra.from") |
  ("$Int $_Wards" as? (Int, _Wards -> IntRange) external "datra.from")
)
```

This is the library declaration; each source already imports it. Calls include
`from (1 + 1) to 5`, `from 2 upwards`, and `from (2, 5)`. Pattern matching selects
the longest complete match and rejects equally long, conflicting matches.
`AST`, `Expr`, `Block`, and `Pages` are library types for syntax captures;
`Block` allows an empty binding sequence, while `Pages` requires a target page.
`NatRange` and `IntRange` describe natural and integer ranges, respectively;
`StringTemplate` describes string templates, including constant strings.
Pattern captures such as `$Int` accept expressions and check their values
against the named type when called. `%Int` remains string-template interpolation.

Unit identifiers obey `$abc = (abc : ())`. The library consequently defines
`nothing` as `let nothing := $Nothing`; `false` and `true` are the ordinary
values `(False : 0)` and `(True : 1)`.

### Named access, scopes, and imports

`.` selects a named field and retains its name and specification:

```datra
{a : Nat := 5, b : String}.a
# a : Nat := 5
```

Use `[1]` on that field to access its payload. Optional names, `~>` / `<~`, and
`of` retain their usual meaning. Missing and ambiguous fields are errors.

`this` returns the current block's declared public fields. A leading `_` makes
a binding private; closures can retain it, but it is absent from `this` and
module exports. A module exports its result; use `yield this` to export its
scope, as `standard_library.datra` does:

```datra
# library_one.datra
_privateOffset := 4
increment := ({value? : Int} -> Int do yield value + _privateOffset)
yield this
```

```datra
import "library_one"
yield LibraryOne.increment 7
```

`import "library_one"` exposes its namespace only. `import all "library_one"`
adds its public bare names as well; collisions are rejected. Relative paths are
resolved from the importing file; `.datra` may be omitted. Filename components
become PascalCase namespaces, so `standard_library.datra` becomes
`StandardLibrary`. Import cycles and missing files are errors.

Every source implicitly imports `all "standard_library"`. Its actual Datra
source is embedded when building the executable, so rebuilding picks up edits
and the executable works from other directories. Qualified syntax such as
`StandardLibrary.if false then (1 + "bad") else 11` retains lazy evaluation.
Bare `StandardLibrary.if` selects the named field containing its explicit sum
of syntax functions.

### Read and save files

The production container works in `/data`, so Datra's normal defaults are:

- `input.datra`
- `output.datra.ast`
- `output.datra`
- `output.datra.error` when parsing or interpretation fails

From this directory, create an example input and run the whole pipeline,
saving both outputs to the host:

```sh
mkdir -p resources
printf '%s\n' '(1; 2 + 3)' > resources/input.datra

docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data:Z" \
  datra-haskell:prod build \
  --input input.datra \
  --ast-output output.datra.ast \
  --output output.datra

cat resources/output.datra.ast
cat resources/output.datra
```

This writes `(<:> 1 (+ 2 3))` to `resources/output.datra.ast` and `(1; 5)`
to `resources/output.datra`. The input creation step replaces
`resources/input.datra`; skip it to use your own source file.

The user mapping makes the generated files belong to your host account. The
`:Z` mount option labels the example directory for container access on
SELinux systems such as Fedora. If Docker requires administrator access,
use `sudo docker run` in place of `docker run`.

Running the image without a command or arguments performs the same pipeline
using the default filenames above.

To use another directory, place `input.datra` in it and mount it at `/data`:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "/absolute/path/to/files:/data" \
  datra-haskell:prod
```

## Generate only an AST

Generate an AST from inline Datra source:

```sh
docker run --rm datra-haskell:prod \
  ast --source '(1; 2 + 3)' --output -
```

Expected output:

```text
(<:> 1 (+ 2 3))
```

Generate an AST from a mounted source file:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data" \
  datra-haskell:prod ast \
  --input input.datra \
  --output output.datra.ast
```

## Interpret an AST directly

Interpret inline canonical AST syntax:

```sh
docker run --rm datra-haskell:prod \
  interpret --ast '(<:> 1 (+ 2 3))' --output -
```

Interpret a mounted AST file:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data" \
  datra-haskell:prod interpret \
  --input output.datra.ast \
  --output output.datra
```

Add `--locale romanian` or `--locale english` to commands that interpret an AST.

## Use the development image

Build the optional `development` target to include GHC, Cabal, Z3, and the build
caches. This image is larger than the default runtime image:

```sh
docker build --target development --tag datra-haskell:development .
docker run --rm --entrypoint cabal datra-haskell:development --version
docker run --rm --entrypoint ghc datra-haskell:development --version
docker run --rm --entrypoint z3 datra-haskell:development --version
```

Open a shell with the repository mounted separately from `/data`:

```sh
docker run --rm --interactive --tty \
  --entrypoint bash \
  --volume "$PWD:/workspace" \
  --workdir /workspace \
  datra-haskell:development
```

Inside the container, use the Docker project file so Cabal does not read the
host-only compiler paths:

```sh
cabal build --project-file=cabal.docker.project all -fliquid -j1
cabal test --project-file=cabal.docker.project all -fliquid -j1
```

## Run locally without Docker

The repository-local toolchain remains available through the ordinary project
file:

```sh
cabal build all -fliquid -j1
cabal test all -fliquid -j1
cabal run -- \
  --input resources/input.datra \
  --ast-output resources/output.datra.ast \
  --output resources/output.datra
```
