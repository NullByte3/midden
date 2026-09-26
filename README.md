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

## Benchmark

midden 0.1.0 compared with Eclipse MAT 1.17, JProfiler 16.2.1 and the VisualVM 2.2.2 heap engine,
run on 8 CPUs with 4 GiB of memory. Each dump was in the page cache before its runs,
and the tables show the best of 2 or 3 runs.

### Cold first run

Time from start to a finished result, with no index or cache on disk. MAT is parse plus Leak
Suspects. JProfiler is `jpanalyze -retained=true`, which builds the index its GUI opens but writes no report.

| Dump | Objects | midden | midden, 1 thread | MAT | JProfiler | VisualVM |
|---|---:|---:|---:|---:|---:|---:|
| Paper server, 938 MB | 11.2 M | **1.95 seconds** | 3.62 seconds | 20.95 seconds | 12.05 seconds | 55.8 seconds |
| mixed-small, 414 MB | 4.1 M | **0.68 seconds** | 1.21 seconds | 7.09 seconds | 4.11 seconds | 772 seconds |
| mixed-1g, 1.2 GB | 11.8 M | **1.79 seconds** | 3.41 seconds | 17.15 seconds | 10.25 seconds | over 1,800 seconds, stopped |
| arrays-1g, 1.2 GB | 37 k | **0.10 seconds** | 0.33 seconds | 1.84 seconds | 0.97 seconds | 0.37 seconds |
| chain-8m, 429 MB | 8.0 M | **0.89 seconds** | 1.36 seconds | 12.26 seconds | 7.01 seconds | 23.8 seconds |
| small-20m, 945 MB | 19.2 M | **6.92 seconds** | 14.95 seconds | 45.71 seconds | 33.46 seconds | 334 seconds |

midden was 7 to 18 times faster than MAT and 5 to 10 times faster than JProfiler, and it was faster on a
single thread than either of them on eight. MAT's full three-report run (suspects, overview and top
components) took 26 to 38 seconds on Paper.

### Reopening an indexed dump

| Dump | midden | MAT | JProfiler |
|---|---:|---:|---:|
| Paper | 1.66 seconds | 30.59 seconds | **1.54 seconds** |
| small-20m | 6.74 seconds | 18.80 seconds | **3.94 seconds** |

JProfiler reopens faster on the large dumps because its analysis stores the dominator tree. midden's
cache only stores the parse, so it saves at most 0.3 seconds.

### Memory

Peak RSS on Paper: midden 1.0 GB, JProfiler 1.3 GB, MAT 2.1 to 3.3 GB (at its 3 GB heap), VisualVM 3.5 GB.


### Features

| | midden | MAT | JProfiler | VisualVM |
|---|---|---|---|---|
| Retained sizes and dominator tree | yes | yes | yes | yes |
| Leak suspects report | yes, objects and classes, with the accumulation point | yes | no, biggest objects view | no |
| Path from a GC root, with field names | yes, printed for every suspect | yes | yes, in the GUI | yes, in the GUI |
| Thread, frame and line that roots an object | yes | yes | in the GUI | in the GUI |
| Class histogram, shallow and retained | yes, also by package | yes | yes | yes |
| Collection fill ratios and empty collections | yes | yes | yes, inspections | through OQL |
| Duplicate strings and arrays | yes | yes | yes, inspections | through OQL |
| Thread locals, class loaders | yes | yes | class loaders | not checked |
| Soft, weak and phantom references | excluded by default, `--include-soft` and `--include-weak` | followed | excluded, options to keep | followed |
| Unreachable objects | reported separately | dropped, option to keep | dropped, option to keep | not checked |
| Direct buffers | yes | through OQL | not checked | through OQL |
| Compare two dumps | `--baseline` | histogram compare in the GUI | `jpcompare` and the GUI | yes, in the GUI |
| Query objects | `--class`, `--object`, `--find`, `--where`, `--shell` | OQL | heap walker filters | OQL |
| Reads gzip, tar and zip | yes | gzip | no | not checked |
| Headless report | yes, text or `--json` | yes, HTML zips | no, index only, results over MCP | no |
| Index cache | yes | yes | yes | yes |
| Needs a JVM | no, one static binary | yes | yes | yes |
| License | MIT | EPL 2.0 | commercial | GPL 2 with Classpath Exception |

## Development

CI runs `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings`.
## License

MIT, see [LICENSE](LICENSE).
