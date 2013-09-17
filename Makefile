all: cabal-build

cabal-build:
	cd src \
	&& cabal configure \
	&& cabal build

deps:
	cabal install she
