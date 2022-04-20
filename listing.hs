{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}


module Cardano.PlutusExample.AlwaysSucceeds
  ( alwaysSucceedsScript
  , alwaysSucceedsScriptShortBs
  , scrAddress
  ) where

import           Cardano.Api.Shelley (PlutusScript (..), PlutusScriptV1)

import           Codec.Serialise
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Short as SBS

--import qualified Plutus.V1.Ledger.Scripts as Plutus
--import qualified PlutusTx
--import           PlutusTx.Prelude hiding (Semigroup (..), unless)

import           Control.Applicative         (Applicative (pure))
import           Control.Monad               (void)
import           Data.Default                (Default (def))
import           Ledger                      (POSIXTime, POSIXTimeRange, PubKeyHash, ScriptContext (..), TxInfo (..),
                                              Validator, pubKeyHash, txId, scriptAddress)
import qualified Ledger
import           Ledger.Contexts             (TxOut,txSignedBy,txOutDatumHash, valuePaidTo)
import qualified Ledger.Interval             as Interval
import qualified Ledger.Scripts              as Scripts
import qualified Ledger.TimeSlot             as TimeSlot
import qualified Ledger.Typed.Scripts        as Scripts hiding (validatorHash)
import           Ledger.Value                as Value
import           Ledger.Bytes                (LedgerBytes(LedgerBytes), fromHex)
import           Ledger.Ada                  as Ada
import           Ledger                      (findOwnInput, txInInfoResolved, txOutValue, pubKeyHashAddress, pubKeyOutput)
import qualified PlutusTx
import           PlutusTx.Prelude            hiding (Applicative (..), Semigroup (..))
import           Prelude                     (Semigroup (..), Show,String)
import qualified Prelude                     as Haskell
import           GHC.Generics                (Generic)
import           Data.Aeson                  (ToJSON, FromJSON)
import           Data.String                 (IsString(fromString))

data Listing = Listing 
    { 
        lseller :: !PubKeyHash
        ,lprice :: !Integer
        ,lcurrency :: !CurrencySymbol
        ,ltokenName :: !TokenName
        ,lcreator :: !PubKeyHash
        ,lroyalty :: !Integer
    } deriving (Show , Generic , ToJSON , FromJSON) 

instance Eq Listing where
        {-# INLINABLE (==) #-}
        a == b = (lseller a == lseller b) &&
                 (lprice a == lprice b) &&
                 (lcurrency a == lcurrency b) &&
                 (ltokenName a == ltokenName b) &&
                 (lcreator a == lcreator b) &&
                 (lroyalty a == lroyalty b)

PlutusTx.unstableMakeIsData '' Listing 
PlutusTx.makeLift '' Listing

data Action = Buy | Cancel
    deriving Show 

PlutusTx.unstableMakeIsData '' Action 
PlutusTx.makeLift '' Action

{-# INLINABLE getAsset #-}
getAsset :: Listing -> AssetClass
getAsset listing =  AssetClass(lcurrency listing,ltokenName listing )

pkhFromStr :: String -> PubKeyHash   
pkhFromStr s =
    case fromHex (fromString s) of 
        Right (LedgerBytes bytes) -> Ledger.PubKeyHash bytes 
        Left msg -> traceError "Could not convert from hex to bytes"

platform :: PubKeyHash
platform = pkhFromStr "6e3c45ce486cff2e089a0f9a2d6d0579f893861b1e250a7650265069"

mkListingValidator ::PubKeyHash -> Listing -> Action -> ScriptContext -> Bool
mkListingValidator platform d redeemer ctx = 
            traceIfFalse "wrong input value" correctInputValue && 
            case redeemer of 
                Buy ->
                    traceIfFalse "wrong token" (correctToken) && 
                    traceIfFalse "price is not correct" (correctPay)
                Cancel -> 
                    traceIfFalse "not signed by seller" (signedBySeller) 
        where
            info :: TxInfo
            info = scriptContextTxInfo ctx

            txnInput :: TxOut 
            txnInput = case findOwnInput ctx of
                    Nothing -> traceError "missing input"
                    Just i -> txInInfoResolved i

            iA :: Integer
            iA = valueOf (txOutValue txnInput) Ada.adaSymbol Ada.adaToken

            correctToken :: Bool
            correctToken = assetClassValueOf (txOutValue txnInput) (getAsset d) >= 1

            correctInputValue :: Bool
            correctInputValue =
                        let
                            isScriptInput i = case (txOutDatumHash . txInInfoResolved) i of
                                Nothing -> False
                                Just _ -> True
                            xs = [i | i <- txInfoInputs info, isScriptInput i]
                        in
                            case xs of
                                [i] -> True
                                _   -> traceError "expected exactly one script input"
            
            signedBySeller :: Bool
            signedBySeller = txSignedBy info (lseller d)

            abs :: Integer -> Integer
            abs n = if n >= 0 then n else negate n

            checkValue :: PubKeyHash -> Integer -> Bool
            checkValue p i = (valueOf (valuePaidTo info (p)) Ada.adaSymbol Ada.adaToken) >= i
            
            percentageValue :: Integer -> Integer -> Integer -> Integer
            percentageValue p v i= PlutusTx.Prelude.divide (p * v) (100*i) 
                    
            correctPay :: Bool 
            correctPay =  let
                            platformFee :: Integer 
                            platformFee = (PlutusTx.Prelude.max (percentageValue 1 (lprice d) 1) 1000000)

                            royaltyAmount :: Integer
                            royaltyAmount = case ((lseller d) == (lcreator d)) of 
                                        True -> 0
                                        False -> (PlutusTx.Prelude.max (percentageValue (lroyalty d) (lprice d) 100) 1000000)  
                          in
                              (checkValue (platform) (platformFee)) &&
                              (checkValue (lcreator d) royaltyAmount) &&
                              (checkValue (lseller d) ((lprice d)-royaltyAmount - platformFee+iA))

data ListingType 
instance Scripts.ValidatorTypes ListingType where
        type instance DatumType ListingType = Listing
        type instance RedeemerType ListingType = Action 

listingTypedValidator :: Scripts.TypedValidator ListingType
listingTypedValidator = Scripts.mkTypedValidator @ListingType
                        ($$(PlutusTx.compile [|| mkListingValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode platform)
                        $$(PlutusTx.compile [|| wrap||])
                    where 
                        wrap = Scripts.wrapValidator 

listingValidator :: Validator
listingValidator = Scripts.validatorScript listingTypedValidator

listingAddress :: Ledger.ValidatorHash
listingAddress = Scripts.validatorHash listingValidator

script :: Scripts.Script
script = Scripts.unValidatorScript listingValidator

scrAddress :: Ledger.Address
scrAddress = scriptAddress listingValidator

alwaysSucceedsScriptShortBs :: SBS.ShortByteString
alwaysSucceedsScriptShortBs = SBS.toShort . LBS.toStrict $ serialise script

alwaysSucceedsScript :: PlutusScript PlutusScriptV1
alwaysSucceedsScript = PlutusScriptSerialised alwaysSucceedsScriptShortBs
