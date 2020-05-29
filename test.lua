-- Filesystem is helpful in tests
local lfs = require("lfs")

-- Enable remote debugging
-- local mobdebug = require("mobdebug")
-- mobdebug.basedir(lfs.currentdir())
-- mobdebug.start()

-- Load luaunit
local luaunit = require("luaunit")

-- Load the most recent version of pegreg.lua
package.path =  "src/?.lua;" .. package.path
local pegreg = require("pegreg")

-- Load the test suites
require("test.Suites")


os.exit(luaunit.LuaUnit.run())
