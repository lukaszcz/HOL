#!/bin/sh
# Run a command in this checkout as if it were mounted at the root the build
# was configured with (HOLDIR in tools/Holmake/Systeml.sml).
#
#   root-wrapper.sh COMMAND [ARGS...]
#
# Environment overrides: HOL_CHECKOUT (default: the enclosing git work tree)
# and HOL_CONFIGURED_ROOT (default: HOLDIR from the checkout's Systeml.sml).
# When both are the same path the command is run directly; otherwise bwrap
# binds the checkout at the configured root.  Exit status 2 means the wrapper
# could not set up the mapping.
set -eu
here=${HOL_CHECKOUT:-$(git rev-parse --show-toplevel)}
conf=${HOL_CONFIGURED_ROOT:-$(sed -n 's/^val HOLDIR = "\(.*\)"$/\1/p' \
      "$here/tools/Holmake/Systeml.sml")}
[ -n "$conf" ] || { echo "root-wrapper: no configured root" >&2; exit 2; }
if [ "$conf" = "$here" ]; then
  cd "$here"
  HOLDIR=$conf PATH=$conf/bin:$PATH
  export HOLDIR PATH
  exec "$@"
fi
command -v bwrap >/dev/null ||
  { echo "root-wrapper: needs bwrap to map $here at $conf" >&2; exit 2; }
exec bwrap --bind / / --dev /dev --dir "$(dirname "$conf")" \
  --bind "$here" "$conf" --chdir "$conf" \
  --setenv HOLDIR "$conf" --setenv PATH "$conf/bin:$PATH" -- "$@"
