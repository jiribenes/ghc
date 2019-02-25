#!/usr/bin/env bash

CABAL=cabal
CABFLAGS="--disable-documentation --disable-profiling --disable-library-profiling"

# It is currently more robust to pass Cabal an absolute path to the project file.
PROJ="$PWD/hadrian/cabal.project"

set -euo pipefail

if ! [ -f "$PROJ" ]; then
    echo "Current working directory must be GHC's top-level folder"
    exit 2
fi

if ! type "$CABAL" > /dev/null; then
    echo "Please make sure 'cabal' is in your PATH"
    exit 2
fi

CABVERSTR=$("$CABAL" --numeric-version)
CABVER=( ${CABVERSTR//./ } )

if [ "${CABVER[0]}" -gt 2 -o "${CABVER[0]}" -eq 2 -a "${CABVER[1]}" -ge 2 ];
then
    "$CABAL" --project-file="$PROJ" new-build $CABFLAGS -v0  -j exe:hadrian
    # use new-exec instead of new-run to make sure that the build-tools (alex & happy) are in PATH
    "$CABAL" --project-file="$PROJ" new-exec  $CABFLAGS -v0  hadrian -- \
        --directory "$PWD" \
        "$@"
else
    echo "Cabal version is too old; you need at least cabal-install 2.2"
    exit 2
fi
