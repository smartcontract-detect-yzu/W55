pragma solidity ^0.4.24;

contract DepositFunds {
    mapping(address => uint) public balances;

    function deposit() public payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw() public {
        uint bal = balances[msg.sender];
        require(bal > 0);

        msg.sender.call.value(bal);

        balances[msg.sender] = 0;
    }
}
