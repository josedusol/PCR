import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;

public class PCRKaratsubaTypes {    
    public static Value ToInt(final StringValue str) {
        String s = str.val.toString();
        int x;
        try {
           x = Integer.parseInt(s);
        }
        catch (NumberFormatException e) {
           throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, 
                                   new String[] { "first", "toInt", "string number", String.valueOf(str) });
        }
        return IntValue.gen(x);
    } 
    
    public static Value Log(final IntValue x, final IntValue base) {
        int n = ((IntValue) x).val;
        int b = ((IntValue) base).val;
        
        return IntValue.gen((int) (Math.log(n) / Math.log(b)));
    } 
}