-- | Generic compile-time dispatch for Atlas-map subfederation checks.
--
-- Primitive federation families supply their own proof procedure.  Composite
-- and otherwise unknown families remain explicitly undecided until a sound
-- procedure is added for their construction.
module AtlasMapSubfederation
  ( decideAtlasMapSubfederation
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (AtlasMapFederationUndecidable)
  , AtlasMapFederationExpression (PrimitiveAtlasMapFederation)
  )

decideAtlasMapSubfederation
  :: uncertainty
  -> ( primitive
       -> primitive
       -> AtlasMapFederationDecision refutation uncertainty proof
     )
  -> AtlasMapFederationExpression primitive singleton
  -> AtlasMapFederationExpression primitive singleton
  -> AtlasMapFederationDecision refutation uncertainty proof
decideAtlasMapSubfederation
    _ decidePrimitive
    (PrimitiveAtlasMapFederation source)
    (PrimitiveAtlasMapFederation target) =
  decidePrimitive source target
decideAtlasMapSubfederation uncertainty _ _ _ =
  AtlasMapFederationUndecidable uncertainty
