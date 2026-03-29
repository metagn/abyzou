when (compiles do: import nimbleutils):
  import nimbleutils

echo "building all"
exec "nim c -d:release --gc:orc --d:useMalloc --outdir:bin src/abyzou"
exec "nim c --app:lib -d:release --gc:orc --d:useMalloc --outdir:bin src/abyzou"
echo "done building"
