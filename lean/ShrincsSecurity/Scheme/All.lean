module

public import ShrincsSecurity.Scheme.Params
public import ShrincsSecurity.Scheme.Address
public import ShrincsSecurity.Scheme.Primitives
public import ShrincsSecurity.Scheme.WotsC
public import ShrincsSecurity.Scheme.Structure
public import ShrincsSecurity.Scheme.Tree
public import ShrincsSecurity.Scheme.Tweaks
public import ShrincsSecurity.Scheme.Fxmss
public import ShrincsSecurity.Scheme.Stateless
public import ShrincsSecurity.Scheme.Shrincs
public import ShrincsSecurity.Scheme.Grinding
public import ShrincsSecurity.Scheme.VerifyCount

/-!
# The SHRINCS scheme

`SHRINCS-Security-Analysis.pdf`, Sections 2 and 3: the abstract, typed model of SHRINCS
(parameters, addresses, function families, WOTS+C, grinding analysis of Lemmas 3.1 (ii) and 3.2,
FXMSS structures and trees, the stateless SLH-DSA path reused from VCVio, and the composite
Algorithms 1–3 with Lemma 3.1 (i)).
-/
