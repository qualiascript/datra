# Datra language development

When adding or extending a language construct, always implement its interaction
with optional names, specification (`~>` / `<~`), and subfederation (`of`). These
are required parts of the feature, not deferred follow-up work. Cover these
interactions with regression tests.

Optional names (`a? : T`) allow named or unnamed values; they are distinct from
optional values (`T?`). Preserve that distinction when implementing features.

If the intended semantics are genuinely unclear, stop and ask the user instead
of choosing an interpretation implicitly.

Keep implementations generic and minimize hard-coded cases. Before adding
string-literal dispatch or handling only selected examples, verify that the
special case is part of the intended language semantics rather than an
accidental implementation shortcut.
