-- Typed preorder data, not M2 source: the Lean grammar is not its own oracle.
-- Explicit tags/counts preserve empty/singleton sequences and nested classes.
macauleanEncodeInterpreterValue = v -> (
    cls := class v;
    if cls === ZZ then {"ZZ", toString v}
    else if cls === QQ then {"QQ", toString numerator v, toString denominator v}
    else if cls === Boolean then {"Boolean", toString v}
    else if cls === Nothing then {"Nothing"}
    else if cls === List or cls === Sequence then
        join({toString cls, toString (#v)},
            flatten apply(toList v, x -> macauleanEncodeInterpreterValue x))
    else {"unsupported", toString cls})

registerMethod(server, "evalValueTree", expr -> (
    try (
        v := value expr;
        join({"ok"}, macauleanEncodeInterpreterValue v))
    else {"error"}))
