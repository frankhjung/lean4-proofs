.DEFAULT_GOAL := default

PROJECTS := Irrational Scrapbook
LEAN_PREFIX := $(shell lean --print-prefix 2>/dev/null)
ifeq ($(LEAN_PREFIX),)
$(error Lean not found. Please ensure Lean 4 is installed and available in your PATH.)
endif
LAKE	:= LD_LIBRARY_PATH="$(LEAN_PREFIX)/lib" lake

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
	@$(LAKE) build $(PROJECTS)

clean: ## Clean the build artifacts
	@$(LAKE) clean

update: ## Update the dependencies using Lake
	@echo "elan default $(shell cat lean-toolchain)"
	@$(LAKE) update
