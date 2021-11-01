IPKG = float-utils.ipkg
SOURCE = src/Data/Double/FloatUtils/Chez.idr 
SUPPORT = support/chez/float-utils.ss #support/chez/float-utils.so
BUILD_OPTS = --codegen chez --directive extraRuntime=support/chez/float-utils.ss

.PHONY: install
install: build
	idris2 $(BUILD_OPTS) --install $(IPKG)

.PHONY: install-with-src
install-with-src: build
	idris2 $(BUILD_OPTS) --install-with-src $(IPKG)

.PHONY: build
build: $(IPKG) $(SOURCE) $(SUPPORT)
	idris2 $(BUILD_OPTS) --build $(IPKG)

.PHONY: test
test: $(IPKG) $(SOURCE) $(SUPPORT)
	idris2 $(BUILD_OPTS) --find-ipkg --exec 'test' src/Data/Double/FloatUtils/Chez.idr

.PHONY: repl
repl:
	rlwrap idris2 $(BUILD_OPTS) --find-ipkg src/Data/Double/FloatUtils/Chez.idr

# support/chez/support.so: support/chez/support.sls
# 	./scripts/chez-compile-library $< $@
