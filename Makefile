all: cabal-install

cabal-install: cabal-build
	cd src \
	&& cabal --only install

cabal-build:
	cd src \
	&& cabal configure \
	&& cabal build

deps:
	cabal install she

clean:
	cd src \
	&& cabal clean
