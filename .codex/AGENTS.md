# Datra language development

When adding or extending a language construct, always implement its interaction
with optional names, specification (`~>` / `<~`), and subfederation (`of`). These
are required parts of the feature, not deferred follow-up work. Cover these
interactions with regression tests.

Optional names (`a? : T`) allow named or unnamed values; they are distinct from
optional values (`T?`). Preserve that distinction when implementing features.
