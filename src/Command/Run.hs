module Command.Run where

import Options.Applicative
import System.Process

import qualified Command.Compile as Compile

data Options = Options
  { compileOptions :: Compile.Options
  , commandLineArguments :: [String]
  } deriving (Show)

optionsParserInfo :: ParserInfo Options
optionsParserInfo = info (helper <*> optionsParser)
  $ fullDesc
  <> progDesc "Run a Sixten program"
  <> header "sixten run"

optionsParser :: Parser Options
optionsParser = Options
  <$> Compile.optionsParser
  <*> many
    (argument str
    $ metavar "ARGS.."
    <> help "Command-line options passed to the Sixten program"
    )

run :: Options -> IO ()
run opts = Compile.compile (compileOptions opts) $ \f ->
  callProcess f $ commandLineArguments opts

command :: ParserInfo (IO ())
command = run <$> optionsParserInfo
