import QOI.Fast
import QOI.Cli

def main (args : List String) : IO UInt32 := QOI.Cli.run QOI.Fast.decodeRGBA args
