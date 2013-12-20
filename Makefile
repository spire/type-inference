all: production

# Deps must be manually installed once.
deps: lib-she

production: cabal-install
debug: cabal-install-debug

test:
	mkdir -p tmp
	cd src && runhaskell PatternUnify/Test.lhs 2>&1 | tee ../tmp/test.out
	! grep FAIL tmp/test.out

######################################################################

cabal-install: src/dist

cabal-install-debug: src/prof-dist

SOURCE = $(shell find src -name '*.lhs')
CABAL_INSTALL = \
  ( cd src \
    && cabal install $(CABAL_OPTIONS) ) \
  || { touch --date "@0" $@ ; \
       exit 42 ; }

src/dist: CABAL_OPTIONS += -O
src/dist: $(SOURCE)
	$(CABAL_INSTALL)

# Build in a non-default dir, so that we can have debug and non-debug
# versions compiled at the same time.
#
# Added '--disable-optimization' because '-O' messes with
# 'Debug.Trace.trace' and other 'unsafePerformIO' hacks.
src/prof-dist: CABAL_OPTIONS += --ghc-options="-fprof-auto" --builddir=prof-dist --disable-optimization
src/prof-dist: $(SOURCE)
	$(CABAL_INSTALL)

######################################################################

clean:
	-rm -rf src/dist src/prof-dist

lib/she.git:
	git clone git@github.com:ntc2/she.git lib/she.git

lib-she: lib/she.git
	-cd lib/she.git \
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
