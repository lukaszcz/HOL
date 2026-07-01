#!/usr/bin/env bash
set -euo pipefail

versions=(4.11.2 4.12.4 4.13.0 4.14.1 4.15.3)
build_root="${TMPDIR:-/tmp}/holsmt-z3-build"
install_dir="$HOME/.local/bin"
jobs="$(nproc 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"

usage() {
  cat <<'EOF'
Usage: build_z3_versions.sh [options]

Build representative Z3 source releases with the TPTP frontend and install
versioned binaries:

  ~/.local/bin/z3-<version>
  ~/.local/bin/z3_tptp-<version>

Options:
  --versions "V ..."   Space-separated Z3 versions to build.
  --build-root DIR     Source/build/log directory. Default: /tmp/holsmt-z3-build.
  --install-dir DIR    Destination directory. Default: ~/.local/bin.
  --jobs N             Parallel build jobs. Default: nproc.
  -h, --help           Show this help.
EOF
}

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --versions)
      [ "$#" -ge 2 ] || die "--versions requires an argument"
      read -r -a versions <<<"$2"
      shift 2
      ;;
    --build-root)
      [ "$#" -ge 2 ] || die "--build-root requires an argument"
      build_root=$2
      shift 2
      ;;
    --install-dir)
      [ "$#" -ge 2 ] || die "--install-dir requires an argument"
      install_dir=$2
      shift 2
      ;;
    --jobs)
      [ "$#" -ge 2 ] || die "--jobs requires an argument"
      jobs=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

[ "${#versions[@]}" -gt 0 ] || die "no versions requested"

src_root="$build_root/src"
cmake_root="$build_root/build"
log_root="$build_root/logs"
smoke_file="$build_root/tptp-smoke.p"

mkdir -p "$src_root" "$cmake_root" "$log_root" "$install_dir"
cat >"$smoke_file" <<'EOF'
fof(ax, axiom, p).
fof(goal, conjecture, p).
EOF

printf 'Using %s parallel jobs\n' "$jobs"

for version in "${versions[@]}"; do
  printf '\n==> Z3 %s\n' "$version"

  tarball="$src_root/z3-$version.tar.gz"
  src_dir="$src_root/z3-z3-$version"
  build_dir="$cmake_root/z3-$version"
  url="https://github.com/Z3Prover/z3/archive/refs/tags/z3-$version.tar.gz"

  if [ ! -f "$tarball" ]; then
    printf 'Downloading %s\n' "$url"
    curl -L --fail --retry 3 --retry-delay 2 -o "$tarball.tmp" "$url"
    mv "$tarball.tmp" "$tarball"
  fi

  if [ ! -d "$src_dir" ]; then
    printf 'Extracting %s\n' "$tarball"
    tar -C "$src_root" -xzf "$tarball"
  fi

  case "$build_dir" in
    "$cmake_root"/z3-*) rm -rf -- "$build_dir" ;;
    *) die "refusing to remove unexpected build directory: $build_dir" ;;
  esac

  printf 'Configuring %s\n' "$version"
  cmake -S "$src_dir" -B "$build_dir" \
    -DZ3_BUILD_LIBZ3_SHARED=FALSE \
    -DCMAKE_BUILD_TYPE=Release \
    -G "Unix Makefiles" \
    >"$log_root/cmake-$version.log" 2>&1

  printf 'Building shell %s\n' "$version"
  cmake --build "$build_dir" --target shell --parallel "$jobs" \
    >"$log_root/build-shell-$version.log" 2>&1

  printf 'Building TPTP frontend %s\n' "$version"
  cmake --build "$build_dir" --target z3_tptp5 --parallel "$jobs" \
    >"$log_root/build-tptp-$version.log" 2>&1

  z3_bin="$(find "$build_dir" -maxdepth 5 -type f -name z3 -perm -111 | head -n 1)"
  tptp_bin="$(find "$build_dir" -type f -name z3_tptp5 -perm -111 | head -n 1)"

  [ -n "$z3_bin" ] && [ -x "$z3_bin" ] || die "could not find built z3 for $version"
  [ -n "$tptp_bin" ] && [ -x "$tptp_bin" ] || die "could not find built z3_tptp5 for $version"

  install -m 0755 "$z3_bin" "$install_dir/z3-$version"
  install -m 0755 "$tptp_bin" "$install_dir/z3_tptp-$version"

  "$install_dir/z3-$version" -version
  "$install_dir/z3_tptp-$version" -file:"$smoke_file" | grep -F '% SZS status Theorem' >/dev/null
  file "$install_dir/z3-$version" "$install_dir/z3_tptp-$version"
done

printf '\nInstalled binaries:\n'
for version in "${versions[@]}"; do
  printf '%s\n' "$install_dir/z3-$version"
  printf '%s\n' "$install_dir/z3_tptp-$version"
done
