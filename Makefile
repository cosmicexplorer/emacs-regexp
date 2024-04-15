.PHONY: gen lib test-panic test-src test clean clean-target


CBINDGEN ?= cbindgen
CARGO_LOCK := ./Cargo.lock
FFI_DIR := ./ffi
CBINDGEN_CONFIG := $(FFI_DIR)/cbindgen.toml
RUST_FFI_SOURCES := $(wildcard $(FFI_DIR)/src/*.rs)

FFI_HEADER_DIR := gen
FFI_HEADER := $(FFI_HEADER_DIR)/rex.h
$(FFI_HEADER): $(CARGO_LOCK) $(CBINDGEN_CONFIG) $(RUST_FFI_SOURCES)
	$(CBINDGEN) --config $(CBINDGEN_CONFIG) --lockfile $(CARGO_LOCK) -v -o $@ -- $(FFI_DIR)

gen: $(FFI_HEADER)



CARGO ?= cargo
TARGET_DIR := ./c-target
LIB_DIR := $(TARGET_DIR)/release
# NB: Need to use abspath here instead of realpath, since the path may not exist yet.
ABSOLUTE_LIB_DIR := $(abspath $(LIB_DIR))
LIB_NAME := rex

SHARED_LIB := $(LIB_DIR)/lib$(LIB_NAME).so
STATIC_LIB := $(LIB_DIR)/lib$(LIB_NAME).a
$(SHARED_LIB) $(STATIC_LIB): $(CARGO_LOCK) $(RUST_FFI_SOURCES)
	$(CARGO) build --release -p emacs-regexp-ffi --target-dir $(TARGET_DIR)

lib: $(SHARED_LIB) $(STATIC_LIB)


TEST_SRC_DIR := $(FFI_DIR)/test
TEST_SRC := $(wildcard $(TEST_SRC_DIR)/*.c)
TEST_OUT := $(patsubst %.c,%.test-exe,$(TEST_SRC))

PANIC_TEST_SRC_DIR := $(TEST_SRC_DIR)/panic
PANIC_TEST_SRC := $(wildcard $(PANIC_TEST_SRC_DIR)/*.c)
PANIC_TEST_OUT := $(patsubst %.c,%.test-exe,$(PANIC_TEST_SRC))

DEV_LIB_DIR := $(TARGET_DIR)/debug
DEV_ABSOLUTE_LIB_DIR := $(abspath $(DEV_LIB_DIR))
DEV_SHARED_LIB := $(DEV_LIB_DIR)/lib$(LIB_NAME).so
DEV_STATIC_LIB := $(DEV_LIB_DIR)/lib$(LIB_NAME).a

$(DEV_SHARED_LIB) $(DEV_STATIC_LIB): $(CARGO_LOCK) $(RUST_FFI_SOURCES)
	$(CARGO) build -p emacs-regexp-ffi --target-dir $(TARGET_DIR)

# We use dynamic linking with rpaths here to reduce binary size in the compiled test executables!
%.test-exe: %.c $(FFI_HEADER) $(DEV_SHARED_LIB)
	$(CC) \
		-I$(FFI_HEADER_DIR) \
		-L$(DEV_LIB_DIR) -l$(LIB_NAME) -Wl,-rpath $(DEV_ABSOLUTE_LIB_DIR) \
		-Og -g \
		$< -o $@

test-panic: $(PANIC_TEST_OUT)
	@echo '+++BEGIN PANIC TESTING+++' >&2
	@for f in $^; do \
		printf '%s\n...\n' "<executing: $${f}>"; \
		if ./$${f} 2>&1 \
			| grep -Fq 'ffi/src/methods.rs:31:41: not yet implemented: this always panics!'; then \
			echo 'success!'; \
		else echo 'failed!'; exit 1; fi \
	done >&2

test-src: $(TEST_OUT)
	@echo '+++BEGIN TESTING+++' >&2
	@for f in $^; do \
		printf '%s\n...\n' "<executing: $${f}>"; \
		if ./$${f}; then echo 'success!'; \
		else echo 'failed!'; exit 1; fi \
	done >&2

test: test-panic test-src



clean:
	rm -fv $(FFI_HEADER) $(SHARED_LIB) $(STATIC_LIB)
	rm -fv $(DEV_SHARED_LIB) $(DEV_STATIC_LIB) $(TEST_OUT) $(PANIC_TEST_OUT)

clean-target: clean
	rm -rf $(TARGET_DIR)
