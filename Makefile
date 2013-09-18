all: cabal-install

cabal-install:
	cd src \
	&& cabal install

cabal-build:
	cd src \
	&& cabal configure \
	&& cabal build

deps:
	cabal install she
