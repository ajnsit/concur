// THIS IS AN EXAMPLE ANSTRACTED COMPONENT
// EVENTUALLY WE NEED TO GENERATE THIS FORMAT FROM GHCJS
// DUNNO HOW IMPORTING REACT ETC WILL WORK, OR HOW WE WILL GENERATE A MODULE.
import React from 'react';
import { StyleSheet, Text, View, Button, Alert } from 'react-native';
var Concur = {
  initView: function (self) {
    return mkView(0, self);
  }
};

function mkState(st, self) {
    return {render: mkView(st, self)};
}

function mkView(count, self) {
    return function() {
        const titleText = count<1? "Press me": "You have clicked " + count + " times"
        return (
           <View style={styles.container}>
             <Button
                onPress={() => { self.setState(mkState((count+1), self))}}
                title={titleText}
             />
           </View>
        );
    };
}

const styles = StyleSheet.create({
    container: {
        flex: 1,
        backgroundColor: '#fff',
        alignItems: 'center',
        justifyContent: 'center',
    },
});

export { Concur };
