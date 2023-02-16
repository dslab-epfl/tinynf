FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install -y curl `# to get Rust and C#` \
                       make `# to build` \
                       gnat-12 `# Ada` \
                       clang-14 `# C, and C# NativeAOT` \
                       gcc-12 `# C` \
                       zlib1g `# C# NativeAOT` \
                       cloc `# Code metrics` && \
    curl -O https://packages.microsoft.com/config/ubuntu/22.04/packages-microsoft-prod.deb `# C# ...` && \
    dpkg -i packages-microsoft-prod.deb && \
    rm packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get install -y dotnet-sdk-7.0 `# ... end C#` && \
    ln -s /usr/bin/gcc-12 /usr/bin/gcc `# Set up GCC` && \
    ln -s /usr/bin/clang-14 /usr/bin/clang `# Set up clang` && \
    ln -s /usr/bin/clang /usr/bin/cc `# Rust needs a default C compiler, and so does the makefile for our port I/O wrapper for C#` && \
    ln -s /usr/lib/x86_64-linux-gnu/libstdc++.so.6 /usr/lib/x86_64-linux-gnu/libstdc++.so `# C# NativeAOT looks for this...` && \
    ln -s /usr/lib/x86_64-linux-gnu/libz.so.1 /usr/lib/x86_64-linux-gnu/libz.so `# ...and this` && \
    rm -rf '/var/lib/apt/lists/*' `# Cleanup; don't remove curl as we need it later`

# GNAT does not like being run as root and will sometimes (but not always) delete systemwide shared libraries during `gnat clean`...
RUN useradd --create-home --shell /bin/bash tinynf
USER tinynf
WORKDIR /home/tinynf

# Since we created a user we must install Rust now, not with the deps we install as root, as otherwise Rust won't be available for the user but only for root
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y

COPY --chown=tinynf:tinynf . .

CMD ["bash"]
