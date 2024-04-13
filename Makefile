.PHONY: header lib test clean clean-target


CBINDGEN := cbindgen
CARGO_LOCK := ./Cargo.lock
FFI_DIR := ./ffi
CBINDGEN_CONFIG := $(FFI_DIR)/cbindgen.toml
RUST_FFI_SOURCES := $(wildcard $(FFI_DIR)/src/*.rs)

FFI_HEADER_DIR := $(FFI_DIR)/src
FFI_HEADER := $(FFI_HEADER_DIR)/rex.h
$(FFI_HEADER): $(CARGO_LOCK) $(CBINDGEN_CONFIG) $(RUST_FFI_SOURCES)
	$(CBINDGEN) --config $(CBINDGEN_CONFIG) --lockfile $(CARGO_LOCK) -v -o $@ -- $(FFI_DIR)

header: $(FFI_HEADER)



CARGO := cargo
TARGET_DIR := ./make-target
PROFILE_SUBDIR := release
SHARED_LIB_DIR := $(TARGET_DIR)/$(PROFILE_SUBDIR)
LIB_NAME := rex
SHARED_LIB := $(SHARED_LIB_DIR)/lib$(LIB_NAME).so
$(SHARED_LIB): $(CARGO_LOCK) $(RUST_FFI_SOURCES)
	$(CARGO) build --release -p emacs-regexp-ffi --target-dir $(TARGET_DIR)

lib: $(SHARED_LIB)



TEST_SRC_DIR := $(FFI_DIR)/test
TEST_SRC := $(wildcard $(TEST_SRC_DIR)/*.c)
TEST_OUT := $(patsubst %.c,%.test-exe,$(TEST_SRC))

$(TEST_SRC_DIR)/%.test-exe: $(TEST_SRC_DIR)/%.c $(FFI_HEADER) $(SHARED_LIB)
	$(CC) -I$(FFI_HEADER_DIR) -L$(SHARED_LIB_DIR) -l$(LIB_NAME) $< -o $@

test: $(TEST_OUT)
	@export LD_LIBRARY_PATH="$(realpath $(SHARED_LIB_DIR))"; \
	for f in $^; do \
		printf '%s\n...\n' "executing: $${f}"; \
		if ./$${f}; then echo 'success!'; \
		else echo 'failed!'; exit 1; fi \
	done >&2



clean:
	rm -fv $(FFI_HEADER) $(SHARED_LIB) $(TEST_OUT)

clean-target: clean
	rm -rf $(TARGET_DIR)
