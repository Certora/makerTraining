if [[ "$1" ]]
then
    RULE="--rule $1"
fi

if [[ "$2" ]]
then
    MSG="- $2"
fi

certoraRun \
    src/vat.sol:Vat \
    src/queue.sol:Queue \
    \
    --verify Vat:certora/specs/vat.spec \
    --link Queue:vat=Vat \
    --optimistic_loop \
    --solc solc8.21 \
    --loop_iter 1 \
    $RULE \
    --rule_sanity \
    --msg "$RULE $MSG"
