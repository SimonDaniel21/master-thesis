-- inductive AGENT where
--   | client    : AGENT
--   | server    : AGENT
-- deriving BEq

-- def AGENT_TO_STRING: AGENT -> String
--   | AGENT.client => "client"
--   | AGENT.server => "server"

-- instance AGENT_DEBUG: ToString AGENT where
--   toString := AGENT_TO_STRING
