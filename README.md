# midden

Find what is holding a JVM heap dump's memory: retained sizes, owners, leak suspects. One static
binary, no JDK needed.

It reads `.hprof` dumps from `jcmd`, `jmap` or `-XX:+HeapDumpOnOutOfMemoryError`, gzipped or inside a
tar or zip, and builds the full object graph and dominator tree, so every object has a retained size.

## Install

Every version is on the [releases page](https://github.com/NullByte3/midden/releases) with its
changes and binaries for Linux (static, any distro) and Windows.

```sh
curl -fsSLO https://github.com/NullByte3/midden/releases/latest/download/midden-x86_64-unknown-linux-musl
sudo install midden-x86_64-unknown-linux-musl /usr/local/bin/midden
```

```powershell
Invoke-WebRequest https://github.com/NullByte3/midden/releases/latest/download/midden-x86_64-pc-windows-gnu.exe -OutFile midden.exe
```

Or `cargo install --path .`.

## Usage

```sh
midden server.hprof                          # full report
midden server.hprof --class ObjectMapper     # one class: referrers, owners, root paths
midden server.hprof --object 0x7f3a1234      # one object: fields, owners, what it retains
midden server.hprof --find jdbc:postgresql   # strings containing the text, and who holds them
midden server.hprof --where 'StandardSession.isValid=false'
midden after.hprof --baseline before.hprof   # what grew between two dumps
midden server.hprof --only suspects --json   # for scripts
midden server.hprof --shell                  # drill in without re-reading the file
```

```
  leak suspects  objects or classes retaining ≥10% of the live heap
    1.  983.7MB  64.1%  class Big @0x740920000
          979.5MB  63.8%  static Big.MAP java.util.HashMap @0x740920090
          979.5MB  63.8%  .table java.util.HashMap$Node[8,388,608] @0x77ba00000  ← accumulation point
       keeps  27,999,745 objects: 4,000,000 × int[] 183.1MB | 4,000,000 × HashMap$Node 183.1MB | ...
```

Sections: heap, suspects, biggest, classes, collections, threads, locals, loaders, strings, arrays,
boxed, references, garbage, system, direct and baseline. Pick them with `--only` and `--skip`.
`midden --help` lists every flag.

- Soft, weak and phantom referents do not count as held unless `--include-soft` or `--include-weak`.
- Sizes follow MAT by default. `--sizes compressed` gives HotSpot's compressed-oops footprint.
- The first run caches the index in `<dump>.midden/`, so later runs start at the report. Turn it off
  with `--no-cache`.
- Expect about 90 bytes of RAM per object. The dump itself is streamed.

## Development

CI runs `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings`.

## License

MIT, see [LICENSE](LICENSE).
