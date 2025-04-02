/-
Let's make a program that will go through the file and remove all
#eval and #check from the source code.
-/

def buffer_size : USize := 20 * 1024

-- First we need a file stream
-- Because Lean can't prove that the file can be terminated within the buffer
-- we use partial def
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buffer ← stream.read buffer_size
  if buffer.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buffer
    dump stream
