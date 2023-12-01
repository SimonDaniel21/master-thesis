def main : IO Unit := do
  let chl: IO.Channel String := unsafeIO String
  IO.println "Hello, world!"


#check BaseIO.asTask
--- Channels?
