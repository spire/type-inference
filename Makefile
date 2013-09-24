all: cabal-install

deps: lib-she

cabal-install:
	cd src \
	&& cabal install $(CABAL_OPTIONS)

# Build in a non-default dir, so that we can have debug and non-debug
# versions compiled at the same time.
cabal-install-debug: CABAL_OPTIONS += --ghc-options="-fprof-auto" --builddir=prof-dist
cabal-install-debug: cabal-install

clean:
	cd src \
	&& cabal clean

lib/she.git:
	git clone git@github.com:ntc2/she.git lib/she.git

lib-she: lib/she.git
	cd lib/she.git \
	&& cabal install

######################################################################
# Before reinstalling all my libraries with profiling support I needed
# to use the --only install here (which prevents cabal from doing
# automatic dependency resolution) to avoid problems with conflicting
# reinstalls of Replib or unbound.
#
# Leaving these around in case those problems come back, in which case
# `make cabal-only-install` should be used.

cabal-only-install: cabal-build
	cd src \
	&& cabal --only install

cabal-build:
	cd src \
	&& cabal configure \
	&& cabal build
