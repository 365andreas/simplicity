module BitMachine where

import Control.Monad.State
import Data.Maybe

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
        let (toCopy, active' ) = splitAt n activeR in
        let (toDrop, active'') = splitAt n activeW in
        do
            pushReadFrame (pastR ++ toCopy, active')
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

run :: BState a -> Maybe BitState
run sth = execStateT sth $ S [] []
