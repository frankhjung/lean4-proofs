.DEFAULT_GOAL := default

PROJECTS := Irrational Scrapbook
LEAN_PREFIX := $(shell lean --print-prefix 2>/dev/null)
ifeq ($(LEAN_PREFIX),)
$(error Lean not found. Please ensure Lean 4 is installed and available in your PATH.)
endif
LAKE	:= LD_LIBRARY_PATH="$(LEAN_PREFIX)/lib" lake
CD	:= cd

.PHONY:	all build clean default lint help update

default: build ## Default goal: build project

all: build ## Build project proofs

help: ## Show this help message
	@echo ""
	@echo "Default goal: ${.DEFAULT_GOAL}"
	@awk 'BEGIN { \
	FS = ":.*##"; \
	printf "\nUsage:\n  make \033[36m<target>\033[0m\n\nTargets:\n"} \
	/^[a-zA-Z_-]+:.*?##/ \
	{ printf "  \033[36m%-10s\033[0m %s\n", $$1, $$2 }' \
	$(MAKEFILE_LIST)

lint: ## Lint the project
	@$(LAKE) lint --lint-only $(PROJECTS)

build: ## Build the project using Lake
	@$(LAKE) exe cache get
	@$(LAKE) build $(PROJECTS)

doc: ## Generate documentation using Lake
	$(CD) docbuild && \
	$(LAKE) build $(addsuffix :docs,$(PROJECTS))

clean: ## Clean the build artifacts
	@$(LAKE) clean

# To upgrade to a new stable Lean version (e.g. v4.32.0):
#
#   1. Find the latest stable release at:
#      https://github.com/leanprover/lean4/releases
#
#   2. Install the toolchain:
#      elan toolchain install leanprover/lean4:v4.32.0
#      elan default leanprover/lean4:v4.32.0
#
#   3. Update lean-toolchain files:
#      echo 'leanprover/lean4:v4.32.0' > lean-toolchain
#      cp lean-toolchain docbuild/lean-toolchain
#
#   4. Update rev pins in lakefiles to match:
#      - lakefile.toml:         rev = "v4.32.0"  (Mathlib)
#      - docbuild/lakefile.toml: rev = "v4.32.0"  (doc-gen4)
#
#   5. Delete stale manifests and regenerate:
#      rm -f lake-manifest.json docbuild/lake-manifest.json
#      make update
update: ## Update the dependencies using Lake
	@echo "elan default $(shell cat lean-toolchain)"
	@$(LAKE) exe cache get
	@$(LAKE) update
	@$(CD) docbuild && \
	$(LAKE) exe cache get && \
	$(LAKE) update
