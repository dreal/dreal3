function outname = jsonbuild(jsonfile)
% By: Houssam Abbas & Matthew O'Kelly
% outname = jsonbuild(jsonfile)
% Read json file and create a mat from it containing all its
% contents.
% The mat is called outname (and has a .mat extension).
% The mat contains a struct array called signal, which ahs one element per
% signal in the json file. 
% Each struct has keys signalName, timesteps and intervals. The last 2 are
% cells of intervals (an interval is a 2-element array).

fid = fopen([jsonfile,'.json']);
tline = fgetl(fid);
nkeys = 0;
nlines = 0;
while ischar(tline)
    %fprintf('%s\n',tline)
    nlines = nlines+1;
    if mod(nlines,2000)==0
        disp(num2str(nlines))
    end
    key = regexp(tline, 'key": "(?<signalName>\w+)"', 'names');
    tokens = regexp(tline, '"time":\s+(?<timestep>\[.*\]),\s+"enclosure":\s+(?<interval>\[.*\])', 'names');
    if ~isempty(key)
        nkeys = nkeys + 1;
        disp(key.signalName);
        i2 = 0; % initialize counter of timesteps
        signal(nkeys).signalName = key.signalName;
        signal(nkeys).timesteps = [];
        signal(nkeys).intervals = [];
    elseif ~isempty(tokens)
        %"time": [0, 0], "enclosure": [0, 0]},
        i2=i2+1;
        signal(nkeys).timesteps{i2} = str2num(tokens.timestep);
        signal(nkeys).intervals{i2} = str2num(tokens.interval);
    end

    tline = fgetl(fid);
end

fclose(fid);
outname = [jsonfile, '.mat'];
save(outname, 'signal')
disp(['Wrote ',outname])