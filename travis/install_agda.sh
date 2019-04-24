#!/bin/sh

VERSION=2.6.1
CURRENT=$(agda -V | sed "s/Agda version \([^-]*\).*/\1/")

if ! type "agda" > /dev/null || [ ! "$CURRENT" = "$VERSION" ]; then
  cabal update
  cabal install alex happy cpphs
  git clone https://github.com/agda/agda --depth=1
  cd agda
  cabal install
  cd ..
  mkdir -p $HOME/.agda
  cp libraries $HOME/.agda/
  cd $HOME/.agda/
  git clone https://github.com/agda/agda-stdlib
  cd agda-stdlib
  git checkout experimental
  cd -
fi
