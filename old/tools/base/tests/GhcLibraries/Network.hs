module Network where


data PortID = PortNumber PortNumber
            | UnixSocket String
         -- | ...
data Socket
type PortNumber=Int
type HostName=String

accept::Socket->IO (Handle,HostName,PortNumber)
accept=undefined

listenOn::PortId->IO Socket
listenOn=undefined

connectTo :: HostName->PortId->IO Handle
connectTo = undefined

withSocketsDo :: IO a -> IO a
withSocketsDo = id
