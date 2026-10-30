import Regula.Site.Artifact
import Regula.Site.Standard

/-! # Site builder entry point

Command-line entrypoint of the rule-reference site builder (`lake exe site`). -/

/-- `site build` builds and checks the Pages artifact at `_site`, and `site standard HTML DOCS`
checks the rendered standard. -/
def siteMain (args : List String) : IO UInt32 := do
  match args with
  | ["build"] =>
    Regula.Site.Build.build
    return 0
  | ["standard", html, docs] =>
    Regula.Site.Standard.check (← Regula.Site.rootDirectory) html docs
    IO.println "site standard: PASS (the rendered standard defines each anchor that the registry \
      and the documentation link, its checklist rows are exactly Regula.checklistRows, each cited \
      section has a source file, and each rule ID in its prose links to its rule page)"
    return 0
  | _ =>
    IO.eprintln "usage: lake exe site build"
    IO.eprintln "       lake exe site standard HTML DOCS"
    return 2

/-- `siteMain` on the command-line arguments. -/
def main : List String → IO UInt32 :=
  siteMain
