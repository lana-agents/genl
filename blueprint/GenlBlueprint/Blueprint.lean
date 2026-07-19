import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import GenlBlueprint.Chapters.Heights
import GenlBlueprint.Chapters.BoundsOnHeights
import GenlBlueprint.Chapters.GaloisActions
import GenlBlueprint.Chapters.PrimesOfPrescribedSize

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Arithmetic Elliptic Curves in General Position" =>

This Blueprint tracks a formalisation of S. Mochizuki, *Arithmetic elliptic curves in
general position*, Math. J. Okayama Univ. *52* (2010), 1–28. The primary target is
Theorem 2.1 of the paper, the equivalence between the Effective Mordell/ABC/Vojta
conjecture for arbitrary hyperbolic curves over number fields and the ABC conjecture for
compactly bounded subsets of the tripod; the implication (ii) ⇒ (i) is formalised in the
`Genl` library relative to an abstract height formalism, and the remaining chapters track
the ingredients needed to instantiate that formalism as well as the results of §3 and §4
of the paper.

{include 0 GenlBlueprint.Chapters.Heights}
{include 0 GenlBlueprint.Chapters.BoundsOnHeights}
{include 0 GenlBlueprint.Chapters.GaloisActions}
{include 0 GenlBlueprint.Chapters.PrimesOfPrescribedSize}

{blueprint_graph}
{blueprint_summary}
