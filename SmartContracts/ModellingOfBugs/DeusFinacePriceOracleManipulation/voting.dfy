/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "./NonNativeTypes.dfy"
include "./Contract.dfy"
include "./Token.dfy"

import opened NonNativeTypes

// datatype Msg = Msg(sender: Account, value: uint256)

// type Address = Account
datatype Proposal  = Proposal (sTime : uint160,  newOwner :Address)
datatype block = block (timestamp: uint160)

class Vote {
  var votingToken : map<Address,uint256>;
  var owner:Address;
  var proposal: Proposal;
  var block :block;
  ghost var totalamount : nat;

  method propose(msg:Msg)
    modifies this
    requires proposal.sTime == 0

  {
    proposal := Proposal(block.timestamp, msg.sender);
  }
  method vote(amount : uint, msg:Msg)
    requires proposal.sTime as nat + 2  > block.timestamp as nat
    requires (if msg.sender in votingToken then votingToken[msg.sender] else 0) as nat + amount as nat < MAX_UINT256
    modifies this
  {

    votingToken := votingToken[msg.sender :=(if msg.sender in votingToken then votingToken[msg.sender] else 0) + amount]; // transfer from sender to this contract using token's method.
    totalamount := totalamount + amount as nat;
  }

  method end(msg:Msg)
    modifies this
    requires proposal.sTime != 0
    requires proposal.sTime as nat + 2  < block.timestamp as nat
    //  requires sum(votingToken) == totalamount as nat
  {
    //  require(votingToken.balanceOf(address(this))*2 >
    //  votingToken.totalSupply(), "vote failed");
    assert(sum(votingToken) == totalamount);
    owner := proposal.newOwner;
  }
  constructor(msg: Msg)
  {
    votingToken := map[];
    owner := msg.sender;
    proposal := Proposal(0,msg.sender);
  }
}

