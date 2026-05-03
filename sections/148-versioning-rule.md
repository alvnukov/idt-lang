## 148. Versioning Rule

`PROTOLANGUAGE.md` is the canonical entry point.

The canonical theory body lives in `sections/`.

No new full-copy theory version files should be created for normal development.

Each accepted version is:

1. edit `PROTOLANGUAGE.md` only for map/status changes;
2. edit the relevant files in `sections/`;
3. commit;
4. annotate git tag.

Version numbers must follow semantic versioning:

`MAJOR.MINOR.PATCH`

Git tags use the same version with a leading `v`, for example:

`v6.0.0`

Version increments:

1. bump `MAJOR` for a new incompatible theory baseline or canonical
   reinterpretation;
2. bump `MINOR` for a backward-compatible extension, new section cluster, or
   new verifier capability;
3. bump `PATCH` for corrections, clarifications, and verifier/test fixes that
   do not change the accepted theory surface.

Do not add versioned full-copy files to the public repository.

Historical full-file states remain recoverable through git tags after public
development begins.
