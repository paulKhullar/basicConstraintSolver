package solver;
/**
 * class to keep track of timing of solvers
 */
public class TimeManager {
   long duration;
   public void start() {
    duration = System.currentTimeMillis();
   }
   public void stop() {
    duration = System.currentTimeMillis() - duration;
   }
   public long getElapsedTime() {
      return duration;
   } 
}
