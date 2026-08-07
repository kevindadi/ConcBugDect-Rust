FROM rustlang/rust:nightly

WORKDIR /workspace

RUN apt-get update \
    && apt-get install -y --no-install-recommends git \
    && rm -rf /var/lib/apt/lists/*

# RustPTA (default nightly) + Miri
RUN rustup component add rust-src rustc-dev llvm-tools-preview miri

# lockbud and AtomVChecker each pin a specific nightly
RUN rustup toolchain install nightly-2026-02-07 \
    && rustup component add --toolchain nightly-2026-02-07 rust-src rustc-dev llvm-tools-preview \
    && rustup toolchain install nightly-2023-03-09 \
    && rustup component add --toolchain nightly-2023-03-09 rust-src rustc-dev llvm-tools-preview

# Sibling layout (not under /workspace):
#   /workspace     -> RustPTA
#   /opt/lockbud   -> lockbud
#   /opt/atomvchecker -> AtomVChecker (from rust-atomic-study)
RUN git clone --depth 1 https://github.com/CodeSentryAI/lockbud.git /opt/lockbud \
    && cd /opt/lockbud \
    && CARGO_TARGET_DIR=/opt/lockbud/target cargo +nightly-2026-02-07 install --path . --locked

RUN git clone --depth 1 https://github.com/AtomVChecker/rust-atomic-study.git /opt/atomvchecker \
    && cd /opt/atomvchecker/section-5-detection/AtomVChecker \
    && CARGO_TARGET_DIR=/opt/atomvchecker/target cargo +nightly-2023-03-09 install --path . --locked

COPY . /workspace
RUN cargo install --path .

ENTRYPOINT ["bash"]
