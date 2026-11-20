# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below and is anchored in Bitcoin block
976796 (2026-11-20 23:27:07 UTC).

| file | SHA-256 |
|---|---|
| `abc-log-bound-subexponential-v1.pdf` | `00c43dae4f42f3b79eb09e16654a5e7c9a4fe129c1b56f9025568a0f236d95c0` |
| `abc-log-bound-subexponential-v1.tar.gz` | `1b87427a0372b01507b833debbfecaeeba9bf17a03b5a268def8a1d328ec687b` |
| `abc-log-bound-subexponential-v1-lean.tar.gz` | `b7934ea5e552034dfd85efb655d3d45f8f56f654cf04379d21a2d6e462099fc9` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
