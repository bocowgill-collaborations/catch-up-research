# Recovered compiled maximum-companion module

These are immutable archival inputs, **not** dependencies imported by the verified
library. The readable proof is [here](../../../CatchUp/ReplyMaximumCompanion.lean).
The [manifest](../../../verification/reply-maximum-companion.json) pins both
original SHA-256 hashes, declaration names, recovery context and editorial changes.

- `ReplyMaximumCompanion.olean`: original Lean 4.27.0 compiled module, 202,696 bytes.
  Its declarations are deserialized and individually rechecked by the kernel,
  without loading its historical imported environment. Deserialization alone is
  not a validity check. Do not load unknown compiled artifacts as trusted imports.
- `ReplyMaximumCompanion.ilean`: original JSON declaration/source-location metadata,
  13,333 bytes. This is not the lost source or an independent proof certificate.

The original raw trace and setup contain private machine paths and are not
published. Their original hashes are retained in the manifest; local private
backups also retain generated C, which is not executed. The published files were
scanned for private paths and credential patterns and were not edited.

The missing August scratch file has a different name and reported source hash.
This archive does not establish that it is the same file or recover its tactic
text. See [CU-R001](../../../results/reply-maximum-companion.md) for the exact
conditional theorem and [verification](../../../verification/reply-maximum-companion.md)
for replay and source-comparison instructions.
