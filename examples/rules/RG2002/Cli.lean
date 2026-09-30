/-! # Command-line entry point

The entry point of the `cli` executable, whose root module belongs to library `Example`. -/

/-- Exit successfully without effects. -/
def main : IO Unit := pure ()
