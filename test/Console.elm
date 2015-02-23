module Main where

import IO.Runner (Request, Response, run)
import ElmTest.Runner.Console (runDisplay)
import Test (tests)

console = runDisplay tests

port requests : Signal Request
port requests = run responses console

port responses : Signal Response
