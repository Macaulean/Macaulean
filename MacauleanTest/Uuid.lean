import MRDI.Uuid

#guard (Option.some "f81d4fae-7dec-11d0-a765-00a0c91e6bf6") == toString <$> (toUuid? "f81d4fae-7dec-11d0-a765-00a0c91e6bf6")

#guard (randUuid (mkStdGen 0)).1 == (0xbf9837e6468a41dfa270aea8d4a747e8 : BitVec 128)
