# Float utils

Currently only Chez is supported.

## Build & install

```sh
make build
make install
```

## Usage

```idris
import Data.Double.FloatUtils.Chez

main : IO ()
main = do
  let out = decodeDouble 4.5
  printLn "m=\{out.mantissa} e=\{out.exponent} s\{out.sign}"
```
