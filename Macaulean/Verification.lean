import Macaulean.Verification.Views
import Macaulean.Verification.ViewLaws
import Macaulean.Verification.Contracts
import Macaulean.Verification.Snapshot
import Macaulean.Verification.Intent
import Macaulean.Verification.Index
import Macaulean.Verification.Frontend
import Macaulean.Verification.Server

/-!
# M2-first intent review

`import Macaulean.Verification; open M2` adds semantic indexing and InfoView
contract panels while retaining the existing M2 execution semantics.

This module does not run agents, approve any project contract, create proof
obligations as axioms, or accept proof results. Those are distinct later stages.
-/
