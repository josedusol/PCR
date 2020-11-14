import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;

public class PCRKaratsubaTypes {    
    public static Value Log(final IntValue x, final IntValue base) {
        int n = ((IntValue) x).val;
        int b = ((IntValue) base).val;
        
        return IntValue.gen((int) (Math.log(n) / Math.log(b)));
    } 
}