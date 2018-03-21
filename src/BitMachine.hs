{-# LANGUAGE GADTs #-}

module BitMachine where

import Control.Monad.State
import Data.Maybe
import Prelude hiding (read)
import Simplicity

type BitType = Maybe Int

-- | List of bits splitted so that active cursor is the
-- first elem of the second list.
type Frame = ([BitType], [BitType])

-- | First list is read stack and second is write stack.
data BitState = S [Frame] [Frame]
    deriving Show

type BState a = StateT BitState (Maybe) a

nop :: BState ()
nop = return ()

throw :: BState a
throw = lift Nothing

-- | Checks if poping will empty the Frame stack.
isPopable :: [Frame] -> Bool
isPopable    []  = False
isPopable (_:[]) = False
isPopable     _  =  True

pushWriteFrame :: Frame -> BState ()
pushWriteFrame top = do
    S r w <- get
    put $ S r $ top : w

pushReadFrame :: Frame -> BState ()
pushReadFrame top = do
    S r w <- get
    put $ S (top : r) w

popWriteFrame :: BState Frame
popWriteFrame = do
    S r (w : ws) <- get
    put $ S r ws
    return w

popReadFrame :: BState Frame
popReadFrame = do
    S (r : rs) w <- get
    put $ S rs w
    return r

write :: Int -> BState ()
write b =
    if (b /= 0) && (b /= 1) then
        throw
    else do
        (past, active) <- popWriteFrame
        case active of
            -- checks if cursor points to undefined.
            -- moves cursor by passing it to the past list
            Nothing:rest -> pushWriteFrame (past ++ [Just b], rest)
            _ -> throw

copy :: Int -> BState ()
copy n = do
    (pastR, activeR) <- popReadFrame
    (pastW, activeW) <- popWriteFrame
    if n > length activeR || n > length activeW then
        throw
    else
        let (toCopy, _       ) = splitAt n activeR in
        let (toDrop, active'') = splitAt n activeW in
        do
            pushReadFrame (pastR, activeR)
            -- check if all are undefined (== Nothing)
            case catMaybes toDrop of
                [] -> pushWriteFrame (pastW ++ toCopy, active'')
                _  -> throw

skip :: Int -> BState ()
skip n = do
    (past, active) <- popWriteFrame
    -- n - 1 so as to be able to go to the end of list
    if n - 1 > length active then
        throw
    else
        let (past', active') = splitAt n active in
        pushWriteFrame (past ++ past', active')

fwd :: Int -> BState ()
fwd n = do
    (past, active) <- popReadFrame
    if n - 1 > length active then
        throw
    else
        let (past', active') = splitAt n active in
        pushReadFrame (past ++ past', active')

bwd :: Int -> BState ()
bwd n = do
    (past, active) <- popReadFrame
    let len = length past
    if n > len then
        throw
    else
        let (past', active') = splitAt (len - n) past in
        pushReadFrame (past', active' ++ active)

newFrame :: Int -> BState ()
newFrame n = do
    let active = replicate n Nothing
    pushWriteFrame ([],active)

moveFrame :: BState ()
moveFrame = do
    S _ w <- get
    if isPopable w then
        do
            (past, active) <- popWriteFrame
            pushReadFrame ([], past ++ active)
    else
        throw

dropFrame :: BState ()
dropFrame = do
    S r _ <- get
    if isPopable r then popReadFrame >> return ()
                   else throw

read :: BState Int
read = do
    (past, curr : active) <- popReadFrame
    case curr of
        Just x -> pushReadFrame (past ++ [curr], active) >> return x
        _      -> throw

-- | Writes 100 and then takes first 2 bits
bitExample :: BState ()
bitExample =   nop
            >> newFrame 5
            >> newFrame 3
            >> write 1
            >> write 0
            >> write 0
            >> moveFrame
            >> copy 2

bitExample' :: BState ()
bitExample' = newFrame 8 >> newFrame 8 >> write 0 >> write 0 >> write 0 >> write 1 >> moveFrame >> newFrame 1 >> translate Simplicity.not

run :: BState a -> Maybe BitState
run sth = execStateT sth $ S [] []

-- bitSize :: SimplicityType -> Int
-- bitSize  U        = 0
-- bitSize (a :+: b) = 1 + max (bitSize a)  (bitSize b)
-- bitSize (a :*: b) = bitSize a + bitSize b

bitSize :: SimplicityValue a -> Int
bitSize  Un      = 0
bitSize (P a b)  = bitSize a + bitSize b
bitSize (L a)    = 1 + bitSize a
bitSize (R b)    = 1 + bitSize b

-- padl :: SimplicityType -> Int
-- padl a b := max (bitSize a) (bitSize b) − bitSize a

-- padr :: SimplicityType -> Int
-- padr a b := max (bitSize a) (bitSize b) − bitSize b

-- | Assuming that words are 8-bit long.
wordSize :: Int
wordSize = 1

rep :: SimplicityValue a -> [BitType]
rep  Un     = []
rep (P a b) = rep a ++ rep b
rep (L Un)  = [Just 0]
rep (L a)   = let l = rep a in Just 0 : replicate (wordSize - length l) Nothing ++ l
rep (R Un)  = [Just 1]
rep (R b)   = let l = rep b in Just 1 : replicate (wordSize - length l) Nothing ++ l

translate :: SimplicityExpr a b -> BState ()
translate  Iden      = copy wordSize
translate  Unit      = nop
translate (Comp s t) = newFrame wordSize >> translate s >> moveFrame >> translate t >> dropFrame
translate (Injl t)   = write 0 >> translate t -- skip _ >> translate t
translate (Injr t)   = write 1 >> translate t -- skip _ >> translate t
translate (Case s t) = do
    b <- read
    case b of
        -- 0 -> fwd (1 + wordSize) >> translate s >> bwd (1 + wordSize)
        -- 1 -> fwd (1 + wordSize) >> translate t >> bwd (1 + wordSize) these are right
        0 -> fwd wordSize >> translate s >> bwd wordSize
        1 -> fwd wordSize >> translate t >> bwd wordSize
        _ -> throw
translate (Pair s t) = translate s >> translate t
translate (Take t)   = translate t
translate (Drop t)   = fwd wordSize >> translate t >> bwd wordSize


