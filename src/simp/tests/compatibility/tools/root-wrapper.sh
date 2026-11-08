#!/bin/sh
# Run a command in this checkout as if it were mounted at the root the build
# was configured with (HOLDIR in tools/Holmake/Systeml.sml).
#
#   root-wrapper.sh COMMAND [ARGS...]
#
# The checkout is the git work tree that contains this script; the command
# runs with that checkout (or the configured root) as its working directory.
# Environment overrides: HOL_CHECKOUT and HOL_CONFIGURED_ROOT (default:
# HOLDIR from the checkout's Systeml.sml).  When both are the same path the
# command is run directly; otherwise bwrap binds the checkout at the
# configured root.  This is not a sandbox: apart from the configured root,
# everything, including /dev/shm, is the host's view.  Directories that the
# mapping had to create on the host are removed afterwards if still empty.
# Exit status 2 means the wrapper was misused or the mapping cannot be set up
# (no bwrap, or the configured root cannot be created); otherwise the status
# is the command's.
[ $# -gt 0 ] ||
  { echo "usage: root-wrapper.sh COMMAND [ARGS...]" >&2; exit 2; }
if [ -n "${HOL_CHECKOUT:-}" ]; then
  here=$HOL_CHECKOUT
else
  here=$(git -C "$(dirname "$0")" rev-parse --show-toplevel 2>/dev/null) ||
    { echo "root-wrapper: not inside a git work tree" >&2; exit 2; }
fi
conf=${HOL_CONFIGURED_ROOT:-}
if [ -z "$conf" ]; then
  [ -f "$here/tools/Holmake/Systeml.sml" ] ||
    { echo "root-wrapper: $here is not a configured HOL checkout" >&2
      exit 2; }
  conf=$(sed -n 's/^val HOLDIR = "\(.*\)"$/\1/p' \
         "$here/tools/Holmake/Systeml.sml")
fi
[ -n "$conf" ] || { echo "root-wrapper: no configured root" >&2; exit 2; }
if [ "$conf" = "$here" ]; then
  cd "$here" || exit 2
  HOLDIR=$conf PATH=$conf/bin:$PATH
  export HOLDIR PATH
  exec "$@"
fi
command -v bwrap >/dev/null ||
  { echo "root-wrapper: needs bwrap to map $here at $conf" >&2; exit 2; }
# Remember which ancestors of $conf do not exist yet: bwrap creates them on
# the host, and they are removed again below (plain rmdir, empty ones only).
created=
p=$conf
while [ "$p" != / ] && [ "$p" != . ] && [ ! -e "$p" ]; do
  created="$created
$p"
  p=$(dirname "$p")
done
if [ -n "$created" ] && [ ! -w "$p" ]; then
  echo "root-wrapper: cannot create $conf: $p is not writable" >&2
  exit 2
fi
bwrap --bind / / --dev-bind /dev /dev \
  --bind "$here" "$conf" --chdir "$conf" \
  --setenv HOLDIR "$conf" --setenv PATH "$conf/bin:$PATH" -- "$@"
status=$?
# $created lists the deepest directory first.
oldifs=$IFS
IFS='
'
set -f
for d in $created; do
  [ -n "$d" ] && rmdir "$d" 2>/dev/null
done
set +f
IFS=$oldifs
exit $status
