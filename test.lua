-- Load luaunit
local luaunit = require("luaunit")

-- Load the most recent version of pegreg.lua
require("pegregpath")
local pegreg = require("pegreg")

-- Load the test suites
require("test.Suites")

os.exit(luaunit.LuaUnit.run())
