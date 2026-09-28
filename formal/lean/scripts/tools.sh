# Sourced by run_comparator.sh and second-kernel.sh. Fetches and builds the pinned external checkers into $TOOLS.
# Pins (same as the verification record in the paper, section 9):
COMPARATOR_REV=fd5d5bcf14177b187f66d4502071268d877887c3   # leanprover/comparator; builds with its own toolchain (v4.35.0-rc3)
EXPORT_REV=076e8e57707e813375e8f9da8bf989799ace9680       # leanprover/lean4export, format 3.1.0, Lean 4.34.1
NANODA_REV=3a2407216ee84a75f9e1aead6803d0578be06ae7       # ammkrn/nanoda_lib 0.4.19
TOOLS="${TOOLS:-$ROOT/.tools}"; mkdir -p "$TOOLS"; TOOLS="$(cd "$TOOLS" && pwd)"

fetch() {  # fetch <dir> <url> <rev>
  if [ ! -d "$TOOLS/$1/.git" ]; then git clone "$2" "$TOOLS/$1"; fi
  git -C "$TOOLS/$1" checkout --quiet "$3"
  [ "$(git -C "$TOOLS/$1" rev-parse HEAD)" = "$3" ] || { echo "$1 is not at the pinned revision $3"; exit 1; }
}
need_lean4export() {
  fetch lean4export https://github.com/leanprover/lean4export "$EXPORT_REV"
  # The pinned commit's own lean-toolchain says v4.34.0, but lean4export must run on the Lean build that wrote the .olean
  # files it reads (otherwise: "failed to read file ... incompatible header"). So build it with this project's toolchain.
  # This is a one-line edit of a file in the tools checkout (not of any source), and the only local change we make to it.
  if ! cmp -s "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"; then
    cp "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"; rm -rf "$TOOLS/lean4export/.lake/build"
  fi
  (cd "$TOOLS/lean4export" && lake build)
  LEAN4EXPORT="$TOOLS/lean4export/.lake/build/bin/lean4export"
}
need_comparator() {
  fetch comparator https://github.com/leanprover/comparator "$COMPARATOR_REV"
  (cd "$TOOLS/comparator" && lake build)
  COMPARATOR_BIN="$TOOLS/comparator/.lake/build/bin/comparator"
}
need_nanoda() {
  fetch nanoda_lib https://github.com/ammkrn/nanoda_lib.git "$NANODA_REV"
  # macOS with a new Xcode SDK: if the link step fails with a `tapi` error mentioning libSystem.B.tbd, build with
  # SDKROOT set to an older SDK, e.g. SDKROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX26.sdk bash scripts/second-kernel.sh
  (cd "$TOOLS/nanoda_lib" && cargo build --release)
  NANODA_BIN="$TOOLS/nanoda_lib/target/release/nanoda_bin"
}
